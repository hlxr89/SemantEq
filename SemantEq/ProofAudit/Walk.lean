import Lean
import SemantEq.Logic
import SemantEq.ProofAudit.Rules

/-!
# The proof-term walk

The role- and polarity-aware walk of a proof term: lambda chains, bindings,
applications dispatched by the head's family (the antecedent, transitions,
records, eliminators, extensionality introductions, bridges, everything
else), the goal-part ablations, and the reading of local bridges' proofs
direction by direction.
-/

namespace SemantEq
namespace ProofAudit
open Lean Elab Meta

/-- A direction `fun h : A => body` of a local bridge's proof is an
implication proof of its own, with `h` in the antecedent's role (every Prop
binder met under `localProofCtx` joins `anteFVars` for the scope of its
body). A proof part of the direction (the body, a constructor component, a
binding's continuation, a conversion's payload) whose type is a goal-spine
proposition other than `True`, mentions no hypothesis, and whose pruned cone
never load-bears on a hypothesis of the direction is a goal part closed
without any hypothesis (`⟨fun _ => qProof, fun _ => pProof⟩` between two
library-true statements). At goal role this fails the proof; at
antecedent-argument role only the direction's conclusion is judged, and one
proved without the hypothesis is the severe grade. A reflexive conclusion is
not a claim; data binders are opened, nested Prop binders join the hypotheses. -/
partial def directionAblation (ctx : Ctx) (role : Role) (memo : IO.Ref (Std.HashMap Expr Bool))
    (locus : String) (concl : Option Expr) (e : Expr) : MetaM Unit := do
  let e := e.headBeta
  -- the part itself (a lambda over a hypothesis is opened instead; a lambda
  -- over data is a proof of a quantified statement, judged as a whole first)
  let hypLam ← match e with
    | .lam _ t _ _ => (isPropSafe t)
    | _ => pure false
  unless hypLam || e.isMData do
    if ← isProofSafe e then
      if let some ty ← inferTypeSafe e then
        -- a conclusion that holds by reflexivity (`x ∈ ↑i ↔ x ∈ i` after a
        -- `simp`, `a = a`) is not a claim; `simp`-built `Set.ext` proofs bind
        -- such hypotheses and never use them
        let refl ← match ty.iff? with
          | some (a, b) => (do if a == b then pure true else isDefEqCheap a b)
          | none => match ty.eq? with
            | some (_, a, b) => (do if a == b then pure true else isDefEqCheap a b)
            | none => pure false
        unless ty.isConstOf ``True || (← anteInvolved ctx ty) do
          -- at goal role: a part on the goal's spine, as opened so far or as
          -- stated (a direction that proves a quantified goal part carries its
          -- own binder); at antecedent-argument role: the direction's conclusion itself,
          -- the fact that meets the antecedent's hypothesis (an auxiliary fact
          -- inside the direction is free not to use the hypothesis)
          let onSpine ← if role == .goal then
              (do if ← isGoalSpineProp ctx ty then pure true else spinePropOf ctx.goalStmt ty)
            else match concl with
              | some c => (do if matchWild c ty then pure true else isDefEqCheap c ty)
              | none => pure false
          -- a reflexive conclusion is not a claim, except when the goal itself
          -- states it: `2 + 2 = 4` as a conjunct of the goal is a part to be
          -- derived like any other
          let exempt := refl && !(role == .goal && onSpine)
          if onSpine && !exempt && !(← lbInvolvedGo ctx memo (← simplifyLogic ctx e)) then
            if role == .goal then
              ctx.fail s!"goal part closes without the bridge's hypothesis ({locus}: {← Meta.ppExpr ty})"
            else
              ctx.severe s!"antecedent hypothesis met by a bridge direction proved without its hypothesis ({locus}: {← Meta.ppExpr ty})"
            return
  -- its structural components
  match e with
  | .mdata _ b => directionAblation ctx role memo locus concl b
  | .lam n t b bi =>
    withLocalDecl n bi t fun y => do
      let isPf ← isPropSafe t
      if isPf then ctx.anteFVars.modify (·.insert y.fvarId!)
      directionAblation ctx role memo locus concl (b.instantiate1 y)
      if isPf then ctx.anteFVars.modify (·.erase y.fvarId!)
  | .letE n t v b _ =>
    -- the binding's value is walked in its own right (at its use); a value
    -- that load-bears on a hypothesis makes its binder one
    withLetDecl n t v fun y => do
      let carries ← lbInvolvedGo ctx memo v
      if carries then ctx.anteFVars.modify (·.insert y.fvarId!)
      directionAblation ctx role memo locus concl (b.instantiate1 y)
      if carries then ctx.anteFVars.modify (·.erase y.fvarId!)
  | .app .. =>
    if let some bind := asBinding? e then
      withLocalDecl bind.binderName bind.binderInfo bind.binderType fun y => do
        let carries ← lbInvolvedGo ctx memo bind.value
        if carries then ctx.anteFVars.modify (·.insert y.fvarId!)
        directionAblation ctx role memo locus concl (bind.mkBody y)
        if carries then ctx.anteFVars.modify (·.erase y.fvarId!)
      return
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := f then
      if (c == ``And.intro || c == ``Iff.intro) && args.size == 4 then
        directionAblation ctx role memo locus concl args[2]!
        directionAblation ctx role memo locus concl args[3]!
      else if c == ``Exists.intro && args.size == 4 then
        directionAblation ctx role memo locus concl args[3]!
      else if (c == ``Eq.mpr || c == ``Eq.mp || c == ``cast) && args.size == 4 then
        directionAblation ctx role memo locus concl args[3]!
      else if c == ``id && args.size == 2 then
        directionAblation ctx role memo locus concl args[1]!
  | _ => pure ()

/-- Is this term a proof of an implication between two propositions? -/
def isImplicationProof (a : Expr) : MetaM Bool := do
  let some ty ← inferTypeSafe a | return false
  let ty ← try whnfR ty catch _ => pure ty
  match ty with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return false
    return (← isPropSafe d) && (← isPropSafe b)
  | _ => return false

/-- Is this term a statement or a family of statements: its type is a sort,
or a function type that ends in one? Such a term is not a derivation, and
whatever proofs occur inside it (the proof fields of a structure that a
statement mentions) are mentions, not steps. -/
def statementLike (e : Expr) : MetaM Bool := do
  let some ty ← inferTypeSafe e | return false
  let ty ← try whnfR ty catch _ => pure ty
  if ty.isSort then return true
  if ty.isForall then
    try
      forallTelescopeReducing ty fun _ b => pure b.isSort
    catch _ => return false
  else return false

/-- Does this (simplified) proof rest on a library fact: a constant graded as
content, or a library theorem that states an equation, a biconditional, a
disequality or a class fact about the subject matter (a lemma of pure logic
is not a fact)? -/
def restsOnLibraryFact (ctx : Ctx) (e : Expr) : MetaM Bool := do
  let equations := !(← getConfig).noHalfEquationFact
  for c in e.getUsedConstantsAsSet do
    if c == ctx.ante || isLocalConst ctx.env c then continue
    let cat ← categorize ctx c
    if cat == .content then return true
    if equations && cat == .bridge then
      if let some (.thmInfo _) := ctx.env.find? c then
        unless ← Meta.isInstance c do return true
  return false

/-- A half: an implication-typed premise of an equation or a biconditional
(the two arguments of `Iff.intro`, of `le_antisymm` on propositions, of any
lemma that concludes `=` or `↔` from implications), met inside a
justification or a local bridge's proof. It is read as an implication proof
of its own with its hypothesis in the antecedent's role, however it is
written: its logical detours are removed first and a half that is not a
function (`Function.const _ p`) is expanded to one. Two things convict it at
goal role: the half as a whole is proved from a library fact, using neither
its hypothesis nor any hypothesis in scope (then the equivalence equates two
statements because both are true), or one of its parts closes a part of the
goal without the hypothesis (`directionAblation`). At antecedent-argument
role both are the severe grade. -/
def auditHalf (ctx : Ctx) (role : Role) (a : Expr) : MetaM Unit := do
  if (← getConfig).noHalves then return ()
  let a1 ← if a.isLambda then pure a else do
    let some ty ← inferTypeSafe a | return ()
    let ty ← try whnfR ty catch _ => pure ty
    match ty with
    | .forallE n d _ bi => pure (.lam n d (.app (a.liftLooseBVars 0 1) (.bvar 0)) bi)
    | _ => return ()
  let .lam n t b bi := a1 | return ()
  unless ← isPropSafe t do return ()
  withLocalDecl n bi t fun h => do
    ctx.anteFVars.modify (·.insert h.fvarId!)
    -- the half's body with its logical detours removed, its hypothesis in
    -- the antecedent's role
    let body ← simplifyLogic ctx (b.instantiate1 h)
    let memo ← IO.mkRef ({} : Std.HashMap Expr Bool)
    unless (← getConfig).noHalfContent do
      if !(← lbInvolvedGo ctx memo body) && (← restsOnLibraryFact ctx body)
          && !(← localityOf ctx (← simplifyLogic ctx body (gate := false))).1 then
        let shown ← match ← inferTypeSafe body with
          | some ty => (do pure (toString (← Meta.ppExpr ty)))
          | none => pure "?"
        if role == .goal then
          ctx.fail s!"a half of an equivalence is proved from a library fact, without its hypothesis ({shown})"
        else
          ctx.severe s!"antecedent hypothesis met through an equivalence one half of which is proved from a library fact, without its hypothesis ({shown})"
    let concl ← if role == .anteArg then inferTypeSafe body else pure none
    directionAblation ctx role memo s!"half with hypothesis {n.eraseMacroScopes}" concl body
    ctx.anteFVars.modify (·.erase h.fvarId!)

/-- Replace the names bound by `have` or `let` by their recorded values. -/
partial def inlineLocalValues (ctx : Ctx) (e : Expr) (fuel : Nat := 6) : MetaM Expr := do
  if fuel == 0 || !e.hasFVar then return e
  let pv ← ctx.propValues.get
  let dv ← ctx.localValues.get
  let e' := e.replace fun x => match x with
    | .fvar id => (pv.get? id).orElse (fun _ => dv.get? id)
    | _ => none
  if e' == e then return e else inlineLocalValues ctx e' (fuel - 1)

/-- Is this record made of library equations and congruence steps only? As
written (with the names bound by `have` replaced by their values) it
mentions no proof variable and no lemma of the file, and no implication
is proved on the spot inside it: no lambda that binds a proof, no
`Iff.intro`, no argument that is a proof of an implication. And once its
lemmas of pure logic are opened, every implication inside uses its
hypothesis, so a lemma that equates two statements because both hold
(`iff_of_true`, `eq_true`) does not make a plain record, while `and_comm`
does. -/
def plainRecord (ctx : Ctx) (r : Expr) : MetaM Bool := do
  let r ← inlineLocalValues ctx r
  if (← localityOf ctx r).1 then return false
  -- no proof variable of any origin: a hypothesis, a case assumption or a
  -- piece of a library fact taken apart could carry an equivalence in
  for fv in (Lean.collectFVars {} r).fvarIds do
    match ← inferTypeSafe (mkFVar fv) with
    | some ty => if ← isPropSafe ty then return false
    | none => return false
  let localLemma (c : Name) : Bool :=
    isLocalConst ctx.env c && (match ctx.env.find? c with | some (.thmInfo _) => true | _ => false)
  if r.getUsedConstantsAsSet.any localLemma then return false
  if r.consumeMData.isAppOf ``Iff.intro then return false
  let bad ← IO.mkRef false
  try
    Meta.forEachExpr r fun sub => do
      match sub with
      | .lam _ d _ _ => if ← isPropSafe d then bad.set true
      | .app _ a =>
        if a.consumeMData.isAppOf ``Iff.intro then bad.set true
        else if ← isImplicationProof a then bad.set true
      | _ => pure ()
    if ← bad.get then return false
    let rs ← simplifyLogic ctx r (gate := false)
    Meta.forEachExpr rs fun sub => do
      if let .lam _ d b _ := sub then
        unless b.hasLooseBVar 0 do
          if ← isPropSafe d then bad.set true
  catch _ => return false
  return !(← bad.get)

/-- Is this proof a hypothesis in scope, or a projection or an application
of one (`h`, `h.1`, `h x`)? A name bound by `have` stands for its value, and
a variable obtained by taking apart a library fact is not a hypothesis. With
`conv`, a conversion of a hypothesis along a plain record counts too
(`Eq.mp e h`, the hypothesis rewritten with library equations: `rw [lemma]
at h`). A proof that merely mentions a hypothesis somewhere is not one. -/
partial def hypothesisCore (ctx : Ctx) (e : Expr) (conv : Bool := false) (fuel : Nat := 32)
    : MetaM Bool := do
  if fuel == 0 then return false
  let e := e.consumeMData.headBeta
  match e with
  | .fvar id =>
    if let some v := (← ctx.propValues.get).get? id then
      return ← hypothesisCore ctx v conv (fuel - 1)
    unless (← getConfig).noLibraryProducts do
      if (← ctx.libraryFVars.get).contains id then return false
    match ← inferTypeSafe e with
    | some ty => isPropSafe ty
    | none => return false
  | .letE _ _ v b _ => hypothesisCore ctx (b.instantiate1 v) conv (fuel - 1)
  | .proj _ _ b => hypothesisCore ctx b conv (fuel - 1)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar _ => hypothesisCore ctx f conv (fuel - 1)
    | .proj _ _ b => hypothesisCore ctx b conv (fuel - 1)
    | .const c _ =>
      if conv && transitionHead c && args.size ≥ 4 then
        return (← plainRecord ctx args[2]!) && (← hypothesisCore ctx args[3]! conv (fuel - 1))
      if let some pi := ctx.env.getProjectionFnInfo? c then
        if pi.numParams < args.size then
          return ← hypothesisCore ctx args[pi.numParams]! conv (fuel - 1)
      return false
    | _ => return false
  | _ => return false

/-- `hypothesisCore` of the proof as written, or of the proof with its
logical detours removed. -/
def hypothesisForm (ctx : Ctx) (a : Expr) : MetaM Bool := do
  if ← hypothesisCore ctx a (conv := true) then return true
  hypothesisCore ctx (← simplifyLogic ctx a (gate := false)) (conv := true)

/-- Is this inductive type a plain bundle: one constructor, not recursive
(`And`, `Exists`, `Nonempty`, a structure)? Taking such a proof apart yields
what was put in. -/
def bundleInductive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo iv) => iv.ctors.length == 1 && !iv.isRec
  | _ => false

/-- Does this elimination (an eliminator or a `match`) take apart a library
fact: one branch, and what is taken apart is a bundle proved with neither
the antecedent nor a proposition in scope behind it? Its products are then
proved facts of the library under local names, not hypotheses. -/
def libraryMajor (ctx : Ctx) (c : Name) (args : Array Expr) : MetaM Bool := do
  if (← getConfig).noLibraryProducts || eqRecFamily c then return false
  let matcher? := Meta.Match.Extension.getMatcherInfo? ctx.env c
  let mut lib := false
  let mut own := false
  let mut branches := 0
  for i in [0:args.size] do
    let a := args[i]!
    unless ← isProofSafe a do continue
    if a.isLambda then
      branches := branches + 1
      continue
    let some ty ← inferTypeSafe a | continue
    let ty ← try whnfR ty catch _ => pure ty
    let .const ind _ := ty.getAppFn | continue
    unless bundleInductive ctx.env ind do continue
    let taken := match matcher? with
      | some mi => mi.numParams + 1 ≤ i && i < mi.numParams + 1 + mi.numDiscrs
      | none => ind == c.getPrefix
    unless taken do continue
    if (← anteInvolved ctx a) || (← localityOf ctx a).1 then own := true else lib := true
  return lib && !own && branches == 1

/-- How many variables the `i`-th argument of the eliminator or matcher `c`
binds, read off the declared type of `c` (the products of that branch). -/
def branchArity (env : Environment) (c : Name) (i : Nat) : Nat := Id.run do
  let some info := env.find? c | return 0
  let mut t := info.type
  for _ in [0:i] do
    match t with
    | .forallE _ _ b _ => t := b
    | _ => return 0
  let .forallE _ d _ _ := t | return 0
  let mut n := 0
  let mut d := d
  repeat
    match d with
    | .forallE _ _ b _ => n := n + 1; d := b
    | _ => break
  return n

/-- The two sides of the equation or biconditional this term proves. -/
def provedSides? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some ty ← inferTypeSafe e | return none
  let ty ← try whnfR ty catch _ => pure ty
  if ty.isAppOfArity ``Iff 2 then return some (ty.getArg! 0, ty.getArg! 1)
  if ty.isAppOfArity ``Eq 3 then return some (ty.getArg! 1, ty.getArg! 2)
  return none

/-- Is this premise a half of the equivalence being built: an implication
from one of its two sides to the other? The premise of a congruence lemma
(`c → x = u` in `ite_congr`) is not: it rewrites a part under a condition. -/
def isHalfOf (a : Expr) (sides : Expr × Expr) : MetaM Bool := do
  let some ty ← inferTypeSafe a | return false
  let ty ← try whnfR ty catch _ => pure ty
  let .forallE _ x y _ := ty | return false
  if y.hasLooseBVars then return false
  let same (p q : Expr) : MetaM Bool := do
    if p == q then pure true else isDefEqCheap p q
  if (← same x sides.1) && (← same y sides.2) then return true
  return (← same x sides.2) && (← same y sides.1)

/-- Is this term a proof of a biconditional? -/
def isIffProof (a : Expr) : MetaM Bool := do
  let some ty ← inferTypeSafe a | return false
  let ty ← try whnfR ty catch _ => pure ty
  return ty.isAppOfArity ``Iff 2

/-- A biconditional used as a justification (the argument of `propext`, of a
lemma that concludes `=` or `↔`, the record of an `Iff.mp` or `Iff.mpr`) may
be assembled from two implications without `Iff.intro` standing there
(`iff_iff_implies_and_implies.mpr ⟨f, g⟩`). It is brought to head normal
form, and when that form is `Iff.intro f g` the two halves are read like any
others. A literal `Iff.intro`, a `have`-bound name and an in-file lemma are
left to the walk, which reads them where they stand. -/
def auditAssembledIff (ctx : Ctx) (role : Role) (e : Expr) : MetaM Unit := do
  if (← getConfig).noHalves || (← getConfig).noSimplify then return ()
  if e.consumeMData.isAppOf ``Iff.intro then return ()
  -- a `have`-bound or in-file restatement is read once, where the walk
  -- reads its proof
  match e.consumeMData.getAppFn with
  | .fvar _ => return ()
  | .const c _ => if isLocalConst ctx.env c then return ()
  | _ => pure ()
  let i ← simpWhnf ctx e
  if i.isAppOfArity ``Iff.intro 4 then
    auditHalf ctx role (i.getArg! 2)
    auditHalf ctx role (i.getArg! 3)

/-- Is this argument a structure assembled on the spot: the constructor of a
structure that is not a typeclass, applied to all its fields? -/
def assembledRecord? (ctx : Ctx) (v : Expr) : Option (ConstructorVal × Array Expr) :=
  match ctorApp? ctx.env v with
  | some (cv, args) =>
    if isStructure ctx.env cv.induct && !isClass ctx.env cv.induct then some (cv, args) else none
  | none => none

/-- Every `Subtype` subterm of a statement (the carriers it speaks of). -/
partial def collectCarriers (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``Subtype 2 then acc.push e else acc
  match e with
  | .app f a => collectCarriers a (collectCarriers f acc)
  | .lam _ t b _ => collectCarriers b (collectCarriers t acc)
  | .forallE _ t b _ => collectCarriers b (collectCarriers t acc)
  | .letE _ t v b _ => collectCarriers b (collectCarriers v (collectCarriers t acc))
  | .mdata _ b => collectCarriers b acc
  | .proj _ _ b => collectCarriers b acc
  | _ => acc

/-- A structure assembled on the spot and handed to the antecedent is read as
transparent: the statement the antecedent delivers is taken with the fields
read off the structure (`S.parts i` is the `H i` that was put in), and the
carriers it then speaks of must be the goal's own. A carrier is the goal's
own when the goal's statement mentions it, or when it is the subtype of an
object of the pair's shared surface, possibly applied to arguments (`↥(H
i)`), with nothing in it from outside that surface. A set built from such an
object (`H i ⊓ H i`) or from none (`⊤`) is a constructed carrier. -/
def reducedCarriersOk (ctx : Ctx) (rty : Expr) : MetaM Bool := do
  let r ← simplifyLogic ctx rty (gate := false)
  let surface ← ctx.surfaceFVars.get
  for t in collectCarriers r do
    if ← occursInGoalStmt ctx t then continue
    if (← surfaceViolation? ctx t).isSome then return false
    -- `Subtype fun x => x ∈ T`: the set `T` must be an object of the surface,
    -- possibly applied to arguments (`H i`), not something built from one
    let .lam _ _ body _ := t.getArg! 1 | return false
    let margs := body.getAppArgs
    unless body.isAppOf ``Membership.mem && margs.size ≥ 2 do return false
    let c1 := margs[margs.size - 2]!
    let c2 := margs[margs.size - 1]!
    let set := if c2.isBVar then c1 else c2
    let .fvar fv := set.getAppFn | return false
    unless surface.contains fv do return false
    let some d ← fv.findDecl? | return false
    let isTy ← try Meta.isType (mkFVar fv) catch _ => pure true
    if isTy || (← isClassSafe d.type).isSome || (← isPropSafe d.type) then return false
  return true

/-- A Prop binder met under a local bridge's proof at a non-side role is the
hypothesis of a direction. It joins `anteFVars` for the scope of its body, and
the outermost such lambda is read as an implication proof of its own. Returns
whether the binder was entered (then `leaveDirection` closes the scope). -/
def enterDirection (ctx : Ctx) (role : Role) (n : Name) (t : Expr) (x : Expr) (body : Expr)
    : MetaM Bool := do
  unless (← ctx.localProofCtx.get) > 0 && role != .side do return false
  unless ← (isPropSafe t) do return false
  ctx.anteFVars.modify (·.insert x.fvarId!)
  if (← ctx.dirCtx.get) == 0 then
    let memo ← IO.mkRef ({} : Std.HashMap Expr Bool)
    let concl ← if role == .anteArg then inferTypeSafe body else pure none
    directionAblation ctx role memo s!"direction with hypothesis {n.eraseMacroScopes}" concl body
  ctx.dirCtx.modify (·+1)
  return true
def leaveDirection (ctx : Ctx) (x : Expr) : MetaM Unit := do
  ctx.dirCtx.modify (·-1)
  ctx.anteFVars.modify (·.erase x.fvarId!)

/-- Options of the lambda-chain walker (`walkLamWith`). -/
structure LamOpts where
  /-- every binder joins `anteFVars`: the products of an antecedent-involved
  elimination -/
  bindersAnte : Bool := false
  /-- the first binders join `libraryFVars`, as many as the counter says:
  the products of taking apart a library fact -/
  libraryLeft? : Option (IO.Ref Nat) := none
  /-- collect the binder ids (the destructuring products' identities) -/
  collect? : Option (IO.Ref (Array FVarId)) := none
  /-- every binder is a pair-aligned surface object: the products of a
  surface-rooted destructuring are the goal's own objects (a witness
  extracted from a surface hypothesis is surface) -/
  markAllSurface : Bool := false
  /-- the goal proof's leading lambdas, or an extensionality introduction (a
  `funext` binder is the goal speaking at the pair-aligned depth): open the
  goal's statement with each binder, mark data binders surface while the
  alignment budget lasts (Prop binders are exempt from the conviction, so
  they neither consume nor need marking), and keep peeling through bindings
  and `mdata`, since the goal's own binders may be intro'd after have/let
  steps -/
  surface : Bool := false
mutual

/-- Peel a lambda chain. Per lambda: open the binder; collect, taint or mark
it per the options (the taint is recorded before `enterDirection`, which
reads it); bump the polarity when the body proves `False`; enter a direction
when the binder is a hypothesis under a local bridge's proof; recurse;
leave. `mdata` is transparent. For any other non-lambda: in `surface` mode
the chain continues through bindings (`handleBinding … true`); in
`markAllSurface` mode it hands over to the surface walker, so conclusion
binders intro'd after an `obtain` still reach the alignment budget;
otherwise to `walk`. -/
partial def walkLamWith (ctx : Ctx) (role : Role) (neg : Nat) (o : LamOpts) (e : Expr)
    : MetaM Unit := do
  match e with
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      if let some acc := o.collect? then acc.modify (·.push x.fvarId!)
      if o.bindersAnte then ctx.anteFVars.modify (·.insert x.fvarId!)
      if let some left := o.libraryLeft? then
        if (← left.get) > 0 then
          left.modify (· - 1)
          ctx.libraryFVars.modify (·.insert x.fvarId!)
      if o.markAllSurface then ctx.surfaceFVars.modify (·.insert x.fvarId!)
      if o.surface then
        -- open the goal's statement with the walk's own fvars
        let rem ← ctx.goalTypeRem.get
        if let .forallE _ d body _ := rem then
          ctx.goalOpenParts.modify (·.push d)
          ctx.goalTypeRem.set (body.instantiate1 x)
        -- data binders consume the alignment budget; Prop binders are exempt
        let isPf ← isPropSafe t
        if !isPf then
          if (← ctx.surfaceLeft.get) > 0 then
            ctx.surfaceLeft.modify (· - 1)
            ctx.surfaceFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body (b.hasLooseBVar 0))
      let hyp ← enterDirection ctx role n t x body
      -- a hypothesis opened inside a justification
      let recHyp ← if ← ablationSuspended ctx then isPropSafe t else pure false
      if recHyp then ctx.recordHyps.modify (·.insert x.fvarId!)
      walkLamWith ctx role neg' o body
      if recHyp then ctx.recordHyps.modify (·.erase x.fvarId!)
      if hyp then leaveDirection ctx x
  | .mdata _ b =>
    -- metadata between two lambdas is transparent in every mode
    walkLamWith ctx role neg o b
  | .letE n t v b _ =>
    if o.surface then
      handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default, b.hasLooseBVar 0⟩ true
    else if o.markAllSurface then walkLamSurface ctx role neg e
    else walk ctx role neg e
  | _ =>
    if o.surface then
      if let some bind := asBinding? e then handleBinding ctx role neg bind true
      else walk ctx role neg e
    else if o.markAllSurface then walkLamSurface ctx role neg e
    else walk ctx role neg e

/-- The plain chain: binders taint when `bindersAnte`. -/
partial def walkLam (ctx : Ctx) (role : Role) (neg : Nat) (bindersAnte : Bool)
    : Expr → MetaM Unit :=
  walkLamWith ctx role neg { bindersAnte }

/-- The chain of an elimination's minor premise: binders collected, tainted
when `bindersAnte`, all surface when `markSurface`. -/
partial def walkLamCollect (ctx : Ctx) (role : Role) (neg : Nat)
    (bindersAnte : Bool) (markSurface : Bool) (acc : IO.Ref (Array FVarId))
    : Expr → MetaM Unit :=
  walkLamWith ctx role neg { bindersAnte, collect? := some acc, markAllSurface := markSurface }

/-- The goal proof's leading lambdas and extensionality introductions: see
`LamOpts.surface`. -/
partial def walkLamSurface (ctx : Ctx) (role : Role) (neg : Nat) : Expr → MetaM Unit :=
  walkLamWith ctx role neg { surface := true }

/-- An antecedent-involved in-file helper (theorem, def or instance) is walked
inline, its body instantiated at the call's arguments, at the call's role and
polarity, so the conjunct ablation, the witness audit and the polarity rules
reach inside it. Capped per helper; beyond the cap the constant grading
stands in. Internal auxiliaries (`_simp_N`, `_proof_N`) are read inline too
when they sit inside a record or a local bridge's proof: the collapse heads
inside them are what convicts there. Returns whether the body was walked. -/
partial def walkInlineHelper (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (f : Expr)
    (args : Array Expr)
    : MetaM Bool := do
  let n := ((← ctx.helperWalks.get).find? c).getD 0
  if n < 2 then
    if let some info := ctx.env.find? c then
      if let some v := valueOf? ctx.env c (allowOpaque := true) then
        let us := match f with | .const _ us => us | _ => []
        let v := v.instantiateLevelParams info.levelParams us
        ctx.helperWalks.modify (·.insert c (n+1))
        if ← auditTrace then IO.eprintln s!"[trace] inline walk of helper {c} @ {role.str}"
        -- the residual lambdas prove the goal part at this position,
        -- so at goal role their binders are the goal's own objects
        let body := (mkAppN v args).headBeta
        if role == .goal then walkLamSurface ctx role neg body
        else walk ctx role neg body
        return true
  return false

/-- The antecedent (or an antecedent-involved local lemma) applied: the
carrier-affinity audit, the data-surface and instance-slot audits of every
surface data slot, the closed-witness audit of its existential hypotheses,
then every argument walks at antecedent-argument role. -/
partial def auditAnteApplication (ctx : Ctx) (neg : Nat) (c : Name) (e : Expr)
    (args : Array Expr)
    : MetaM Unit := do
  -- carrier-affinity audit: a Sort-valued instantiation of the antecedent
  -- that is foreign to the goal's carriers convicts iff it occurs in what the
  -- antecedent delivers here (a dead junk parameter is harmless) and the goal
  -- does not itself existentially bind a Sort
  -- a library fact taken apart and handed to the antecedent is a library
  -- fact meeting a hypothesis of the antecedent with nothing local behind it
  for a in args do
    if let .fvar id := a.consumeMData then
      if (← ctx.libraryFVars.get).contains id then
        if let some ty ← inferTypeSafe a then
          if ← isPropSafe ty then
            let shown ← (do try pure (toString (← id.getUserName).eraseMacroScopes) catch _ => pure "?")
            ctx.flag s!"library fact taken apart ({shown}) feeding ante application"
            ctx.severe s!"outside fact taken apart ({shown}) feeding ante application draws on no local hypothesis"
  if c == ctx.ante then
    let delivered? ← inferTypeSafe e
    if !ctx.goalSortExists then
      for a in args do
        if let some ty ← inferTypeSafe a then
          if ty.isSort && foreignCarrier ctx a then
            if let some rty := delivered? then
              if (rty.find? (· == a)).isSome then
                ctx.fail s!"ante instantiated at a carrier foreign to the goal statement ({← Meta.ppExpr a})"
    -- data-surface audit: the antecedent's surface data slots must be filled
    -- at the goal's own surface objects; an argument capturing an off-surface
    -- data fvar uses the antecedent as a schema at objects the pair never
    -- speaks about. Prop fvars are exempt.
    let slotData ← ctx.anteSlotData.get
    for i in [0:min args.size slotData.size] do
      if slotData[i]! then
        let a := args[i]!
        if a.hasFVar then
          -- instance-slot rule: the antecedent must be applied at the goal's
          -- own structures. A class-typed argument in a data slot whose class
          -- sits on a goal-surface carrier, and which is not the goal's own
          -- instance binder, convicts when the class is not a subsingleton and
          -- the goal binds an instance (a replaced structure), or when it is a
          -- content-bearing subsingleton (`Fintype`) the goal does not grant.
          -- Exempt: defeq to the goal's instance, occurring in the goal's
          -- statement, classically-free scaffolding, granted finiteness.
          if let some clsType ← inferTypeSafe a then
            if let some clsName ← (isClassSafe clsType) then
              let surfSet ← ctx.surfaceFVars.get
              let surfCarrier := clsType.getAppArgs.any fun ca =>
                ca.isFVar && surfSet.contains ca.fvarId!
              let argCore ← resolveLocal ctx a
              let argIsSurfFvar := argCore.isFVar && surfSet.contains argCore.fvarId!
              if surfCarrier && !argIsSurfFvar then
                let mut goalInst : Option FVarId := none
                for fv in surfSet.toList do
                  if goalInst.isNone then
                    if let some d ← fv.findDecl? then
                      if (← isDefEqSafe d.type clsType) then
                        goalInst := some fv
                let defeqGoal ← match goalInst with
                  | some g => isDefEqSafe a (mkFVar g)
                  | none => pure false
                let subsing ← do
                  match ← (try Meta.synthInstance? (← Meta.mkAppM ``Subsingleton #[clsType]) catch _ => pure none) with
                  | some _ => pure true
                  | none => pure false
                -- classically-free scaffolding (`Decidable`, `DecidableEq`):
                -- synthesizable given a universal classical `Decidable` provider?
                let synthCl ← do
                  try
                    let decProv := Expr.forallE `p (mkSort Level.zero)
                      (mkApp (mkConst ``Decidable) (Expr.bvar 0)) BinderInfo.default
                    Meta.withLocalDecl `cd BinderInfo.instImplicit decProv fun cd =>
                      Meta.withNewLocalInstance ``Decidable cd do
                        pure (← Meta.synthInstance? clsType).isSome
                  catch _ => pure false
                -- does the goal statement grant finiteness (`Finite`/`Fintype`)?
                let goalFin := ctx.goalHasFin
                let occGoal := (← occursInGoalStmt ctx a) || (← occursInGoalStmt ctx argCore)
                unless defeqGoal || occGoal do
                  if !subsing then
                    -- a replaced non-subsingleton structure the goal binds
                    if goalInst.isSome then
                      ctx.fail s!"ante instance slot at a surface carrier filled with a replaced {clsName} structure ({← Meta.ppExpr a}); the goal's own instance is unused"
                  else
                    -- a content subsingleton manufactured, the goal grants none;
                    -- classically-free scaffolding stays exempt
                    if !synthCl && !goalFin then
                      ctx.fail s!"ante instance slot at a surface carrier filled with a manufactured {clsName} instance ({← Meta.ppExpr a}) the goal statement does not grant"
          let isSortSlot ← do
            match ← inferTypeSafe a with
            | some ty => pure ty.isSort
            | none => pure false
          if isSortSlot && !ctx.goalSortExists then
            -- a Sort-valued surface slot must be the goal's own carrier (a type
            -- constructed from goal data, `↥(s 0)`, is related but not the same
            -- carrier); `PLift`/`ULift` adapters are content-free, so the wrapped
            -- core is tested, let-bound names resolved first
            let mut core ← resolveLocal ctx a
            while core.isAppOfArity ``PLift 1 || core.isAppOfArity ``ULift 1 do
              core ← resolveLocal ctx (core.getArg! 0)
            let bareSurface := core.isFVar &&
              (← ctx.surfaceFVars.get).contains core.fvarId!
            if !bareSurface then
              -- a type the goal's own statement mentions is the goal's own
              -- object (`↥F` inside `IsAlgebraic F a`)
              if !(← occursInGoalStmt ctx a) && !(← occursInGoalStmt ctx core) then
                if let some rty := delivered? then
                  if (rty.find? (· == a)).isSome then
                    ctx.fail s!"ante carrier slot instantiated at a type constructed from, not identical to, the goal's carriers ({← Meta.ppExpr a})"
          else
            -- a value slot whose argument the delivered conclusion uses as a
            -- type (the coercion `↥arg` appears) induces a carrier, which must
            -- be the goal's own object; plain value use keeps the lenient
            -- transport rule
            let vcore ← resolveLocal ctx a
            let bareSurface := vcore.isFVar &&
              (← ctx.surfaceFVars.get).contains vcore.fvarId!
            let carrierUse :=
              if bareSurface then false
              else match delivered? with
                | some rty =>
                  (rty.find? (fun t =>
                    t.isAppOfArity ``Subtype 2 &&
                    ((t.getArg! 1).find? (· == a)).isSome)).isSome
                | none => false
            if carrierUse then
              -- a structure assembled on the spot is transparent: what counts
              -- is the carriers of the delivered statement once its fields are
              -- read off, and the surface of the data that went into it
              let transparent ← if (← getConfig).noTransparentRecord then pure false else
                match assembledRecord? ctx vcore, delivered? with
                | some _, some rty => reducedCarriersOk ctx rty
                | _, _ => pure false
              if transparent then
                if let some fv ← surfaceViolation? ctx vcore then
                  ctx.fail s!"ante surface slot instantiated at an object outside the statements' shared surface ({← Meta.ppExpr a}; foreign object {← Meta.ppExpr (mkFVar fv)})"
              else if !(← occursInGoalStmt ctx a) && !(← occursInGoalStmt ctx vcore) then
                ctx.fail s!"ante value slot used as a carrier of the delivered statement but instantiated at a constructed object ({← Meta.ppExpr a})"
            else
              if let some fv ← surfaceViolation? ctx a then
                if let some rty := delivered? then
                  if (rty.find? (· == a)).isSome then
                    ctx.fail s!"ante surface slot instantiated at an object outside the statements' shared surface ({← Meta.ppExpr a}; foreign object {← Meta.ppExpr (mkFVar fv)})"
  -- closed-witness audit of the antecedent's existential hypotheses
  if c == ctx.ante && ctx.witnessCheck then
    if let some info := ctx.env.find? c then
      witnessAudit ctx info.type args
  -- the antecedent, or an antecedent-involved local lemma: its arguments
  -- feed the antecedent pipeline
  for a in args do walk ctx .anteArg neg a

/-- A role transition (`Iff.mp` / `Iff.mpr` / `Eq.mp` / `Eq.mpr`): the converted
proof (last argument) inherits the conversion's role; the record
(second-to-last) walks at the enclosing role inside `recordCtx`; an
antecedent-involved record that actually rewrites freezes the converted proof. -/
partial def walkTransitionApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (args : Array Expr)
    : MetaM Unit := do
  -- the record is the third argument and the converted proof the fourth,
  -- whatever further arguments the result is applied to
  let recIdx := 2
  let payIdx := 3
  if args.size > recIdx then
    -- a biconditional converted along is read through its halves when it is
    -- assembled from two implications
    if role != .side && (c == ``Iff.mp || c == ``Iff.mpr) then
      auditAssembledIff ctx role args[recIdx]!
  -- a transition transports the role with the content: the converted proof
  -- (last argument) inherits the conversion's position; the record walks at
  -- the enclosing role inside `recordCtx`, where content is a flag and a
  -- collapsed goal part is refused
  ctx.chainCtx.modify (·+1)
  -- an antecedent-involved justification that actually rewrites freezes the
  -- converted proof
  let recInv ← if args.size > recIdx then
      (do if ← anteInvolved ctx args[recIdx]! then recordRewrites args[recIdx]! else pure false)
    else pure false
  for i in [0:args.size] do
    if i == recIdx then
      ctx.recordCtx.modify (·+1)
      walk ctx role neg args[i]!
      ctx.recordCtx.modify (·-1)
    else if recInv && i == payIdx then
      ctx.frozenCtx.modify (·+1)
      walk ctx role neg args[i]!
      ctx.frozenCtx.modify (·-1)
      frozenPayload ctx role args[i]!
    else walk ctx role neg args[i]!
  ctx.chainCtx.modify (·-1)

/-- Simp's goal-conversion wrappers (`of_eq_true` / `of_eq_false`): the last
argument is a rewrite record, walked at the enclosing role inside
`recordCtx`. -/
partial def walkRecordApp (ctx : Ctx) (role : Role) (neg : Nat) (args : Array Expr)
    : MetaM Unit := do
  ctx.chainCtx.modify (·+1)
  for i in [0:args.size] do
    if i == args.size - 1 then
      ctx.recordCtx.modify (·+1)
      walk ctx role neg args[i]!
      ctx.recordCtx.modify (·-1)
    else walk ctx role neg args[i]!
  ctx.chainCtx.modify (·-1)

/-- An eliminator application: the minors are walked first with their
products collected, a branch is a goal part unless the major is
antecedent-involved, an elimination whose products are all unused earns no
exemption (dead elimination), and an `Eq.rec`-family substitution along an
antecedent-involved equation that rewrites freezes its minor. -/
partial def walkEliminatorApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (args : Array Expr)
    : MetaM Unit := do
  -- an `Eq.rec`-family substitution is a transport position
  if eqRecFamily c then ctx.chainCtx.modify (·+1)
  let mut majorInv := false
  let mut majorSurface := true
  for a in args do
    if !a.isLambda then
      if (← isProofSafe a) && (← anteInvolved ctx a) then majorInv := true
      if a.hasFVar then
        if (← surfaceViolation? ctx a).isSome then majorSurface := false
  -- the minors are walked first, collecting product binders; a destructured
  -- local's occurrence then takes its products' role join
  let products ← IO.mkRef (#[] : Array FVarId)
  let mut minors := #[]
  -- a substitution along an antecedent-involved equation that actually
  -- rewrites freezes its minor (the goal transported by the rewrite)
  let mut majorRewrites := true
  if eqRecFamily c && majorInv then
    for a in args do
      if !a.isLambda then
        if (← isProofSafe a) && (← anteInvolved ctx a) then
          majorRewrites ← recordRewrites a
  let eqFrozen := eqRecFamily c && majorInv && majorRewrites
  if eqFrozen then ctx.frozenCtx.modify (·+1)
  -- taking apart a library fact yields proved facts of the library, not
  -- hypotheses; a case split yields assumptions (`libraryMajor`)
  let majorLib ← libraryMajor ctx c args
  for i in [0:args.size] do
    let a := args[i]!
    if a.isLambda then
      if ← isProofSafe a then
        -- a genuine minor: its binders are the destructuring products
        let left? ← if majorLib then pure (some (← IO.mkRef (branchArity ctx.env c i))) else pure none
        let opts : LamOpts :=
          { bindersAnte := majorInv, libraryLeft? := left?, collect? := some products, markAllSurface := majorSurface }
        walkLamWith ctx role neg opts a
        minors := minors.push a
        if role == .goal && !majorInv then
          branchAblation ctx a s!"branch of {c}"
      else
        -- motive / predicate lambda: type-level, no products to collect, and
        -- nothing to grade unless statements are walked
        if (← getConfig).noSkipStatements || !(← statementLike a) then
          walkLam ctx role neg majorInv a
  -- dead-elimination audit: the ablation exemption for an antecedent-involved
  -- elimination is earned only if some product is used; a destructuring whose
  -- products are all unused distributed nothing, and the default rule resumes
  -- on its branches
  if role == .goal && majorInv && minors.size > 0 then
    let prods ← products.get
    if prods.size > 0 then
      let mut anyUsed := false
      for p in prods do
        if ← usedAnywhere ctx p then anyUsed := true
      if !anyUsed then
        for m in minors do
          branchAblation ctx m s!"branch of {c} (ante destructured to unused products)"
  if eqRecFamily c then ctx.chainCtx.modify (·-1)
  for a in args do
    unless a.isLambda do
      match a with
      | .fvar id =>
        let occ ← ctx.occRoles.get
        let pj := (← products.get).foldl (init := (none : Option Role))
          fun r? pid => match occ.get? pid with
            | some r => some ((r?.map (Role.join r)).getD r)
            | none => r?
        recordOcc ctx id (pj.getD role)
        checkFalseNode ctx neg a "hypothesis of type False"
      | _ => walk ctx role neg a
  if eqFrozen then ctx.frozenCtx.modify (·-1)

/-- An extensionality introduction: the pointwise proof's binders inherit
surface (budgeted) and the proof is a goal part; a motive lambda gets no
surface budget. -/
partial def walkExtIntroApp (ctx : Ctx) (role : Role) (neg : Nat) (args : Array Expr)
    : MetaM Unit := do
  for a in args do
    if a.isLambda then
      if ← isProofSafe a then
        -- the pointwise proof: its binders inherit surface (budgeted)
        walkLamSurface ctx role neg a
        if role == .goal then branchAblation ctx a "lambda argument"
      else
        -- motive / type-family lambda: no surface budget
        if (← getConfig).noSkipStatements || !(← statementLike a) then
          walkLam ctx role neg false a
    else walk ctx role neg a

/-- A bridge applied forward: role-transparent (its hypotheses are
constitutive inputs, not side conditions), the bare-bridge rule at goal
role, and the equational-chain legs (`Eq.trans`, `congrArg`) as transport
positions. -/
partial def walkBridgeApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (e : Expr)
    (args : Array Expr) (isAss isLoc : Bool)
    : MetaM Unit := do
  -- a bridge applied forward is role-transparent: its hypotheses are
  -- constitutive inputs (`le_antisymm h1 h2`), not side conditions. The
  -- bare-bridge rule: a plain Eq/Iff library lemma is licensed to transport
  -- content between phrasings; asserted at goal role outside every transport
  -- position with an antecedent-free cone, its conclusion stands as
  -- mathematical content and the proof fails. Not inside a record or a local
  -- bridge's proof, where a value applies equations bare without asserting
  -- them as goal content.
  if role == .goal && (← ctx.chainCtx.get) == 0 && !isLoc && !isAss
      && !(← ablationSuspended ctx) then
    if ← plainEqIffConcl ctx.env c then
      if !(← anteInvolved ctx e) then
        ctx.fail s!"bridge conclusion asserted as content at goal role (bare, ante-free, outside transport position): {c}"
  let chain := c == ``Eq.trans || c == ``Eq.symm || c == ``Iff.trans ||
    c == ``Iff.symm || c == ``congrArg || c == ``congrFun ||
    c == ``congr || c == ``Trans.trans || c == ``HEq.trans || c == ``HEq.symm
  -- a `match` that takes apart a library fact: its products are marked as
  -- an eliminator's are
  let matchLib ← if Meta.isMatcherCore ctx.env c then libraryMajor ctx c args else pure false
  for i in [0:args.size] do
    let a := args[i]!
    if matchLib && a.isLambda && (← isProofSafe a) then
      let left ← IO.mkRef (branchArity ctx.env c i)
      walkLamWith ctx role neg { libraryLeft? := some left } a
    else if chain then
      ctx.chainCtx.modify (·+1)
      walk ctx role neg a
      ctx.chainCtx.modify (·-1)
    else walk ctx role neg a

/-- An application headed by a constant of no special family: `cast` (a transport
position, frozen when its equation is antecedent-involved and rewrites), the
constructors (`And.intro` / `Iff.intro` / `Exists.intro`: proof-typed lambda
components are the goal's own quantified objects), and everything else; a
lambda argument at goal role is a goal part and is ablated unless the head is
data. -/
partial def walkOtherApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (args : Array Expr)
    (isAss isLoc : Bool)
    : MetaM Unit := do
  let dataHead ← if isAss || isLoc then pure false
    else pure ((← categorize ctx c) == .data)
  if c == ``cast then
    ctx.chainCtx.modify (·+1)
  -- `cast` along an antecedent-involved equation that actually rewrites
  -- freezes its value
  let castFrozen ← if c == ``cast && args.size == 4 then
      (do if ← anteInvolved ctx args[2]! then recordRewrites args[2]! else pure false)
    else pure false
  let ctorHead := c == ``And.intro || c == ``Iff.intro || c == ``Exists.intro
  -- a `match` that takes apart a library fact: its products are marked as
  -- an eliminator's are
  let matchLib ← if Meta.isMatcherCore ctx.env c then libraryMajor ctx c args else pure false
  for i in [0:args.size] do
    let a := args[i]!
    if matchLib && a.isLambda && (← isProofSafe a) then
      let left ← IO.mkRef (branchArity ctx.env c i)
      walkLamWith ctx role neg { libraryLeft? := some left } a
    else if castFrozen && i == 3 then
      ctx.frozenCtx.modify (·+1)
      walk ctx role neg a
      ctx.frozenCtx.modify (·-1)
      frozenPayload ctx role a
    else if ctx.conjunctSurface && role == .goal && ctorHead && a.isLambda
        && (← isProofSafe a) then
      -- `⟨…, fun n => A n⟩`: the component's binders are the goal statement's
      -- own quantified objects (budgeted)
      walkLamSurface ctx role neg a
    else walk ctx role neg a
    if role == .goal && a.isLambda && !dataHead then
      branchAblation ctx a "lambda argument"
  if c == ``cast then ctx.chainCtx.modify (·-1)

/-- The walk of a proof term at a role and polarity: locals record their
occurrence, constants are judged by family, bindings go to `handleBinding`,
lambdas to the chain walker, and applications dispatch on the head. -/
partial def walk (ctx : Ctx) (role : Role) (neg : Nat) (e : Expr) : MetaM Unit := do
  -- a statement, or a family of statements, is not a derivation
  if e.isApp || e.isLambda then
    unless (← getConfig).noSkipStatements do
      if ← statementLike e then return ()
  match e with
  | .bvar _ | .mvar _ | .sort _ | .lit _ => pure ()
  | .fvar id =>
    recordOcc ctx id role
    checkFalseNode ctx neg e "hypothesis of type False"
  | .const c us => do
    let nFlagsBefore := (← ctx.flags.get).size
    if c == ctx.ante then pure ()
    else if ctx.assumed.contains c then judgeOutsideLocal ctx role c
    else if isLocalConst ctx.env c then
      if c.isInternalDetail && !(← ablationSuspended ctx) then expandLocal ctx role neg c
      else if c.isInternalDetail || (← constReaches ctx ctx.reachMemo ctx.ante c) then
        -- inline walk of the helper's body (capped)
        let n := ((← ctx.helperWalks.get).find? c).getD 0
        match (if n < 2 then valueOf? ctx.env c (allowOpaque := true) else none), ctx.env.find? c with
        | some v, some info =>
          ctx.helperWalks.modify (·.insert c (n+1))
          let body := v.instantiateLevelParams info.levelParams us
          if role == .goal then walkLamSurface ctx role neg body
          else walk ctx role neg body
        | _, _ => expandLocal ctx role neg c
      else
        judgeOutsideLocal ctx role c
        if role != .side then walkOutsideLocalProof ctx role neg c
    else judgeConst ctx role neg c "bare constant"
    if role == .anteArg then severeIfClosed ctx nFlagsBefore c #[]
  | .mdata _ b => walk ctx role neg b
  | .proj _ _ b =>
    checkFalseNode ctx neg e "projection"
    walk ctx role neg b
  | .lam .. => walkLam ctx role neg false e
  | .forallE .. => pure ()   -- a Pi in proof position is a type; nothing to judge
  | .letE n t v b _ =>
    handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default, b.hasLooseBVar 0⟩
  | .app .. =>
    if let some bind := asBinding? e then
      handleBinding ctx role neg bind
    else do
      checkFalseNode ctx neg e "application"
      if role == .goal && (← ablationSuspended ctx) then
        if let some ty ← inferTypeSafe e then checkCollapseEquation ctx e ty
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const c _ =>
        -- an ex-falso head fed by a benign `noConfusion` `False` is
        -- impossible-branch elimination: the branch is computationally dead,
        -- so its arguments walk at side role
        if exFalso5.contains c then
          let mut benign := false
          for a in args do
            unless benign do
              if let some ty ← inferTypeSafe a then
                if (← whnf ty).isConstOf ``False then
                  benign ← benignNoConfusionFalse ctx a
          if benign then
            for a in args do walk ctx .side neg a
            return
        -- a `noConfusion`-family discriminator on a derived equation proves
        -- anything from an absurd equation without a `False` node: ex falso at
        -- positive polarity
        if neg == 0 && nameHasNoConfusion c && !isLocalConst ctx.env c then
          unless ← benignNoConfusionFalse ctx e do
            ctx.fail s!"explosion through {c} on a derived equation in positive position"
        -- head judging, by family
        let isAss := ctx.assumed.contains c
        let isLoc := !isAss && c != ctx.ante && isLocalConst ctx.env c
        let locInternal := isLoc && c.isInternalDetail
        let locInvolved ← if isLoc && !locInternal then
            constReaches ctx ctx.reachMemo ctx.ante c
          else pure false
        let isLocFree := isLoc && !locInternal && !locInvolved
        -- an antecedent-involved in-file helper is walked inline at the
        -- call's role and polarity (`walkInlineHelper`); internal auxiliaries
        -- are read inline inside a record or a local bridge's proof, where
        -- their collapse heads are what convicts
        if locInvolved || (locInternal && (← ablationSuspended ctx)) then
          if ← walkInlineHelper ctx role neg c f args then return
        let nFlagsBefore := (← ctx.flags.get).size
        if c == ctx.ante then pure ()
        else if isAss || isLocFree then
          judgeOutsideLocal ctx role c
          -- a bridge-shaped antecedent-free in-file lemma keeps its shape
          -- admission, and its proof is read once at the use role
          if isLocFree && role != .side then walkOutsideLocalProof ctx role neg c
        else if isLoc then expandLocal ctx role neg c
        else judgeConst ctx role neg c "application head"
        -- a fact taken out of a typeclass instance (`Fact.out`) is the
        -- library's fact when nothing local is behind the instance. The
        -- step from an instance to an instance of a parent class is
        -- instance resolution, not a fact.
        unless (← getConfig).noNeClassRecord do
          if let some pi := ctx.env.getProjectionFnInfo? c then
            if pi.fromClass && pi.numParams < args.size && role != .side then
              let inst := args[pi.numParams]!
              let toInstance ← (do match ← inferTypeSafe e with
                | some ty => pure (← isClassSafe ty).isSome
                | none => pure false)
              if !toInstance && (← isProofSafe e) && (← isProofSafe inst)
                  && !(← localityOf ctx inst).1 then
                let shown := match inst.getAppFn with | .const n _ => toString n | _ => "an instance"
                if role == .goal then
                  ctx.flag s!"library fact {shown} with a ≠ or class conclusion used as a step (taken out of the instance by {c})"
                else
                  ctx.flag s!"content import {shown} feeding ante application (taken out of the instance by {c})"
        if role == .anteArg then severeIfClosed ctx nFlagsBefore c args
        -- a goal part collapsed to `True` (or a conjunct dropped) by a content
        -- fact inside a record or a local bridge's proof is a goal part closed
        -- without the antecedent
        if role == .goal && collapseHead c && (← ablationSuspended ctx) then
          for a in args do
            collapseAblation ctx a s!"goal part collapsed by {c} inside a rewrite record or a local bridge's proof" (spine := true)
        -- the same holds of the premises of any lemma there: a part of the
        -- goal proved without the antecedent and handed to a lemma inside a
        -- justification is a goal part closed without the antecedent,
        -- whatever the lemma does with it
        else if role == .goal && c != ctx.ante && !isAss && (← ablationSuspended ctx) then
          unless (← getConfig).noPremiseRule do
            for a in args do
              premiseAblation ctx a s!"premise of {c} inside a rewrite record or a local bridge's proof"
        -- halves: inside a justification or a local bridge's proof, an
        -- argument of a constant whose own statement concludes an equation
        -- or a biconditional, when it is an implication from one side of
        -- that conclusion to the other (`Iff.intro`, an antisymmetry
        -- lemma), is an implication proof of its own, and a
        -- biconditional argument of such a constant (`propext i`) is read
        -- through its two halves when it is assembled from two. An
        -- eliminator whose result merely happens to be an equation is not
        -- such a constant: its minor premises are case branches.
        if role != .side && ((← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0) then
          if ← plainEqIffConcl ctx.env c then
            let sides? ← provedSides? e
            for a in args do
              if ← isImplicationProof a then
                if let some sides := sides? then
                  if ← isHalfOf a sides then auditHalf ctx role a
              else if ← isIffProof a then auditAssembledIff ctx role a
        -- conjunct-level ablation: at goal role the components of `And.intro`
        -- and `Iff.intro` are goal parts, so an atomic or applicative
        -- component (`rfl`, a `decide` term, a goal hypothesis) that closes
        -- without the antecedent is a redundant goal part (`⟨ante, rfl⟩`);
        -- lambda components are ablated by the generic arm. Under a
        -- conversion justified by the antecedent (`frozenCtx`) the components
        -- are the antecedent's residual obligation; there only a component
        -- that the original goal states as a part, closed without the
        -- antecedent, convicts. Not in antecedent-argument position.
        if ctx.conjunctAblation && role == .goal && !(← ablationSuspended ctx)
            && (c == ``And.intro || c == ``Iff.intro) then
          if (← ctx.frozenCtx.get) == 0 then
            for a in args do
              unless a.isLambda do
                branchAblation ctx a s!"constructor component ({c})"
          else unless (← getConfig).noFrozenSpine do
            for a in args do
              unless a.isLambda do
                frozenSpineCheck ctx a s!"constructor component ({c}) under a conversion along the antecedent"
        -- argument dispatch
        if c == ctx.ante || locInvolved then
          auditAnteApplication ctx neg c e args
        else if transitionHead c then
          walkTransitionApp ctx role neg c args
        else if recordHead c then
          walkRecordApp ctx role neg args
        else if let some majorIdx ← projConsumerAnte ctx c args then
          -- a projection consuming an antecedent-derived record: the arguments
          -- after it feed an antecedent-derived fact
          for i in [0:args.size] do
            walk ctx (if i > majorIdx then .anteArg else role) neg args[i]!
        else if ← isEliminatorConst ctx.env c then
          walkEliminatorApp ctx role neg c args
        else if extIntroHead c then
          walkExtIntroApp ctx role neg args
        else if ← headIsBridge ctx c (isAss || isLocFree) then
          walkBridgeApp ctx role neg c e args isAss isLoc
        else
          walkOtherApp ctx role neg c args isAss isLoc
      | .fvar id =>
        recordOcc ctx id role
        let anteHead := (← ctx.anteFVars.get).contains id
        -- the argument of a negated hypothesis is a proof of the un-negated
        -- statement, one negation lower
        let lower ← if !(← getConfig).noNegPolarity && neg > 0 then
            (do match ← inferTypeSafe f with
                | some ty =>
                  let ty ← try whnfR ty catch _ => pure ty
                  pure (ty.isAppOfArity ``Not 1 || (match ty with
                    | .forallE _ _ b _ => b.isConstOf ``False
                    | _ => false))
                | none => pure false)
          else pure false
        for i in [0:args.size] do
          walk ctx (if anteHead then .anteArg else role)
            (if lower && i == 0 then neg - 1 else neg) args[i]!
      | .proj sName _ s =>
        -- Iff/Eq projections are transitions: the record walks at the
        -- enclosing role inside `recordCtx`, the converted proof inherits the
        -- role; other projections follow the projection-consumer rule
        checkFalseNode ctx neg f "projection"
        if sName == ``Iff || sName == ``Eq then
          ctx.chainCtx.modify (·+1)
          ctx.recordCtx.modify (·+1)
          walk ctx role neg s
          ctx.recordCtx.modify (·-1)
          -- an antecedent-involved record that rewrites freezes the converted proofs
          let recInv ← (do if ← anteInvolved ctx s then recordRewrites s else pure false)
          if recInv then ctx.frozenCtx.modify (·+1)
          for a in args do walk ctx role neg a
          if recInv then ctx.frozenCtx.modify (·-1)
          if recInv then
            if let some a := args[0]? then frozenPayload ctx role a
          ctx.chainCtx.modify (·-1)
        else
          walk ctx role neg s
          let inv ← anteInvolved ctx s
          for a in args do walk ctx (if inv then .anteArg else role) neg a
      | _ =>
        walk ctx role neg f
        for a in args do walk ctx role neg a

/-- Bridge-arm test for an application head: globals via `categorize`, assumed
or antecedent-free local lemmas via their graded statement. -/
partial def headIsBridge (ctx : Ctx) (c : Name) (outsideLocal : Bool) : MetaM Bool := do
  if outsideLocal then
    return ((← ctx.localGrade.get).find? c).getD false
  else
    return (← categorize ctx c) == .bridge

/-- The proof converted along the antecedent (the payload of a frozen
conversion) proves the rewritten goal, so it is not ablated as a goal part.
One case still convicts: its type is a part the original goal states, and
its proof is antecedent-free. `(and_iff_right ante).mpr p` hands the part
`p` to the goal without the antecedent having anything to do with it. -/
partial def frozenPayload (ctx : Ctx) (role : Role) (a : Expr) : MetaM Unit := do
  if (← getConfig).noFrozenSpine then return ()
  if role == .goal && !(← ablationSuspended ctx) then
    frozenSpineCheck ctx a "proof converted along the antecedent"

/-- The check behind `frozenPayload` and the constructor components under a
conversion along the antecedent: a proof whose statement is a part the
original goal states, that does not use the antecedent and that rests on no
hypothesis in scope (a library fact, a computation), closes that part of the
goal without the antecedent. A proof that is a hypothesis of the goal, or a
projection, an application or a rewriting with library equations of one
(`hypothesisCore`), is the goal's own material being handed to the
antecedent, and is not convicted. A constructor bundle is judged component
by component, and a proof that is itself a conversion is judged together
with the proof it converts. -/
partial def frozenSpineCheck (ctx : Ctx) (a : Expr) (locus : String) : MetaM Unit := do
  unless ← isProofSafe a do return ()
  let some ty ← inferTypeSafe a | return ()
  if ty.isConstOf ``True then return ()
  if ← anteInvolved ctx ty then return ()
  let a' := a.headBeta
  if a'.isAppOfArity ``And.intro 4 || a'.isAppOfArity ``Iff.intro 4 then
    let args := a'.getAppArgs
    frozenSpineCheck ctx args[2]! locus
    frozenSpineCheck ctx args[3]! locus
    return
  -- what a further conversion inside the converted proof converts is judged
  -- the same way: a part the goal states may not be closed there and then
  -- carried back out by a second conversion
  if let .const c _ := a'.getAppFn then
    let n := a'.getAppNumArgs
    if (transitionHead c || c == ``cast) && n ≥ 4 then
      frozenSpineCheck ctx (a'.getArg! 3) locus
    else if (c == ``Eq.rec || c == ``Eq.ndrec) && n ≥ 6 then
      frozenSpineCheck ctx (a'.getArg! 3) locus
    else if (c == ``Eq.subst || c == ``Eq.casesOn) && n ≥ 6 then
      frozenSpineCheck ctx (a'.getArg! 5) locus
  unless ← isGoalSpineProp ctx ty do return ()
  if ← anteInvolvedLB ctx a then return ()
  if ← hypothesisForm ctx a then return ()
  ctx.fail s!"goal part closes ante-free ({locus})"

/-- Ablation check: at goal role, a proof whose dependency cone and whose
type's cone are both antecedent-free closes a goal part without the
antecedent. -/
partial def branchAblation (ctx : Ctx) (a : Expr) (locus : String) : MetaM Unit := do
  -- inside a rewrite record (a conditional bridge's side conditions, a
  -- `forall_congr` pointwise lambda) or a local bridge's proof the sub-proof
  -- proves the record or the bridge, not the goal: positional goal-part
  -- ablation is suspended there, and only the collapse heads convict
  if ← ablationSuspended ctx then return ()
  collapseAblation ctx a locus

/-- A premise handed to a lemma inside a justification. A function of
objects is opened (`fun _ => p`, the pointwise premise of an extensionality
lemma); a function of proofs is an implication and is left to the reading of
halves. What remains is refused when it proves a part the goal states
outright (not a part under one of its binders) without the antecedent,
unless it is a hypothesis of the goal in some form or draws on the
hypothesis of an implication proved inside the same justification. -/
partial def premiseAblation (ctx : Ctx) (a : Expr) (locus : String) : MetaM Unit := do
  match a.consumeMData with
  | .lam n d b bi =>
    if ← isPropSafe d then return ()
    withLocalDecl n bi d fun x => premiseAblation ctx (b.instantiate1 x) locus
  | a =>
    unless ← isProofSafe a do return ()
    let some ty ← inferTypeSafe a | return ()
    if ty.isConstOf ``True then return ()
    -- a part the goal states outright; a part under one of the goal's
    -- binders is matched too loosely to convict a side condition
    unless ← isGoalSpinePropExact ctx ty do return ()
    if ← hypothesisForm ctx a then return ()
    -- under an implication proved inside the justification, its hypothesis
    -- plays the antecedent's role
    let hyps ← ctx.recordHyps.get
    if a.hasAnyFVar hyps.contains then return ()
    collapseAblation ctx a locus (spine := true)

/-- The dependency-cone test itself (load-bearing involvement):
a proof-typed part whose pruned cone and whose type never reach the antecedent
closes a goal part without it. Used directly for collapse heads, which are
judged even inside a local bridge's proof. -/
partial def collapseAblation (ctx : Ctx) (a : Expr) (locus : String) (spine : Bool := false)
    : MetaM Unit := do
  unless ← isProofSafe a do return ()
  let some ty ← inferTypeSafe a | return ()
  if ty.isConstOf ``True then return ()   -- a proof of `True` carries nothing
  if ← anteInvolved ctx ty then return ()
  -- on the collapse path the position does not certify a goal part: the
  -- collapsed proposition must sit on the goal's spine (`simp [hc]` on an `if`
  -- condition is a reduction, not a part proved)
  if spine then
    unless ← isGoalSpineProp ctx ty do return ()
  -- a constructor bundle is judged part by part (`eq_true ⟨A, X⟩`)
  let a' := a.headBeta
  if a'.isAppOfArity ``And.intro 4 || a'.isAppOfArity ``Iff.intro 4 then
    let args := a'.getAppArgs
    collapseAblation ctx args[2]! locus
    collapseAblation ctx args[3]! locus
    return
  if ← anteInvolvedLB ctx a then return ()
  ctx.fail s!"goal part closes ante-free ({locus})"

/-- Read the proof of a bridge-shaped, antecedent-free in-file lemma once, at
the role where the lemma is used, with goal-part ablations suspended and
content at the flag tier (the shape admission stays the floor); its
directions are read by `directionAblation`. Runs in both modes. -/
partial def walkOutsideLocalProof (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) : MetaM Unit := do
  unless ((← ctx.localGrade.get).find? c).getD false do return ()
  let n := ((← ctx.helperWalks.get).find? c).getD 0
  if n ≥ 1 then return ()
  let some info := ctx.env.find? c | return ()
  let some v := valueOf? ctx.env c (allowOpaque := true) | return ()
  if v.getUsedConstantsAsSet.contains ``sorryAx then return ()
  ctx.helperWalks.modify (·.insert c (n+1))
  ctx.localProofCtx.modify (·+1)
  walk ctx role neg (v.instantiateLevelParams info.levelParams [])
  ctx.localProofCtx.modify (·-1)

/-- A binding (`have`, `let`, a beta-redex): the body is walked at the
enclosing role and ablated after an antecedent-free binding at goal role;
the value is walked at the role of its use. An antecedent-free Prop binding
is an outside lemma: its statement is graded, and when bridge-shaped its
proof is read at the use role. -/
partial def handleBinding (ctx : Ctx) (role : Role) (neg : Nat) (b : Binding)
    (surfaceMode : Bool := false) : MetaM Unit := do
  let vInv ← anteInvolved ctx b.value
  let propT ← isPropSafe b.binderType
  withLocalDecl b.binderName b.binderInfo b.binderType fun x => do
    if vInv then ctx.anteFVars.modify (·.insert x.fvarId!)
    -- a data binding whose value is built from surface objects is
    -- itself a surface object (transitive surface; closed values included)
    if propT then ctx.propValues.modify (·.insert x.fvarId! b.value)
    if !propT then
      ctx.localValues.modify (·.insert x.fvarId! b.value)
      if !b.value.hasFVar || (← surfaceViolation? ctx b.value).isNone then
        ctx.surfaceFVars.modify (·.insert x.fvarId!)
    let body := b.mkBody x
    let neg' := neg + (← negBump body b.bodyUses)
    if surfaceMode then walkLamSurface ctx role neg' body
    else walk ctx role neg' body
    -- ablation locus (i): the rest of the proof after this binding
    if role == .goal && !(← ablationSuspended ctx) then
      if !(← anteInvolvedLB ctx body) then
        if ← isProofSafe body then
          let tyOk ← do
            match ← inferTypeSafe body with
            | some ty => pure !(← anteInvolved ctx ty)
            | none => pure false
          if tyOk then
            ctx.fail s!"goal part closes ante-free (body after binding {b.binderName})"
    let jr := ((← ctx.occRoles.get).get? x.fvarId!)
    -- a binding used only inside records or local bridge proofs is judged in
    -- that regime: its value is walked at the record's role under `recordCtx`
    let jrRec := ((← ctx.recordOccRoles.get).get? x.fvarId!)
    let walkAtUse (v : Expr) : MetaM Unit := do
      match jr, jrRec with
      | some r, _ => walk ctx r neg v
      | none, some r =>
        ctx.recordCtx.modify (·+1); ctx.chainCtx.modify (·+1)
        walk ctx r neg v
        ctx.chainCtx.modify (·-1); ctx.recordCtx.modify (·-1)
      | none, none => walk ctx role neg v
    if vInv then
      if ← auditTrace then IO.eprintln s!"[trace] ante-involved binding {b.binderName} walked @ {((jr.getD (jrRec.getD role))).str}{if jr.isNone && jrRec.isSome then " (record use)" else ""}"
      walkAtUse b.value
    else if propT then
      -- an antecedent-free Prop local is an outside lemma; sorry scan on the value
      if ← auditTrace then do
        let jrs := (jr.map Role.str).getD "unused"
        IO.eprintln s!"[trace] RULE2 have {b.binderName} jr={jrs}"
      if ← reachesSorry ctx b.value then ctx.sorryHit.set true
      if ← bridgeGradeType ctx.env b.binderType then
        -- a local bridge is admitted; flag it if it quotes the goal
        if ← goalShaped ctx b.binderType then
          ctx.flag s!"goal-shaped local bridge (have {b.binderName})"
        -- the shape admission is the floor; the bridge's proof is read at its
        -- use role, with goal-part ablations suspended (it proves the bridge,
        -- not the goal) and content at the flag tier, while a goal part
        -- collapsed inside it is refused and each direction is read as an
        -- implication proof of its own (`directionAblation`), in both modes
        match jr.orElse (fun _ => jrRec) with
        | some r =>
          if r != .side then
            ctx.localProofCtx.modify (·+1)
            walk ctx r neg b.value
            ctx.localProofCtx.modify (·-1)
        | none => pure ()
      else
        match jr with
        | some .goal =>
          -- a fact that is a hypothesis in scope in another form (a
          -- projection, an application, or the hypothesis rewritten with
          -- library equations) is the goal's own material: it is read by
          -- its own proof at the place of use, with goal-part ablations
          -- suspended (the proof proves the fact, not the goal) and a
          -- library fact on its derivation failing as on the goal's, inside
          -- a record included. Any other fact is refused where it is used:
          -- what it brings is not the goal's.
          let rests ← if (← getConfig).noLocalFactRead then pure false
            else hypothesisForm ctx b.value
          if rests then
            ctx.localFactCtx.modify (·+1)
            walk ctx .goal neg b.value
            ctx.localFactCtx.modify (·-1)
          else
            ctx.fail s!"bare-Prop local hypothesis {b.binderName} used on goal spine"
        | some .anteArg =>
          ctx.flag s!"bare-Prop local hypothesis {b.binderName} feeding ante application"
          let (prop, data) ← localityOf ctx b.value
          unless prop do
            let note := if data then "" else ", nor on any local variable"
            ctx.severe s!"bare-Prop local hypothesis {b.binderName} feeding ante application is proved without any local hypothesis{note}"
        | some .side => pure ()
        | none =>
          match jrRec with
          | some .goal =>
            -- a side condition of a conditional rewrite: tolerated and recorded
            ctx.flag s!"bare-Prop local hypothesis {b.binderName} used inside a rewrite record or a local bridge's proof"
          | some .anteArg =>
            ctx.flag s!"bare-Prop local hypothesis {b.binderName} feeding ante application"
            let (prop, data) ← localityOf ctx b.value
            unless prop do
              let note := if data then "" else ", nor on any local variable"
              ctx.severe s!"bare-Prop local hypothesis {b.binderName} feeding ante application is proved without any local hypothesis{note}"
          | _ => pure ()
    else
      walkAtUse b.value
end

/-- Split a goal conclusion into its ∧-parts (goal-part support). -/
partial def splitAnd (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``And 2 then
    splitAnd (e.getArg! 1) (splitAnd (e.getArg! 0) acc)
  else acc.push e

/-- The ∧-parts of the goal's conclusion (`Ctx.goalParts`). -/
def computeGoalParts (goalType : Expr) : MetaM (Array Expr) := do
  try
    let (_, _, concl) ← forallMetaTelescope goalType
    return splitAnd concl
  catch _ => return #[]
end ProofAudit
end SemantEq
