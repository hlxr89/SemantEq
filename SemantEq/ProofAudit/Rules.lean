import Lean
import SemantEq.Logic
import SemantEq.ProofAudit.Ctx

/-!
# The checker's node-level rules

Polarity (`negBump`, `checkFalseNode`), bindings, the transition / record /
collapse heads, load-bearing involvement of the antecedent (`lbInvolvedGo`),
the pair-aligned surface and carrier tests, the goal's propositional spine,
the closed-witness audit, the locality of a use (the severe tier).
-/

namespace SemantEq
namespace ProofAudit
open Lean Elab Meta

/-- `False` constructed at positive polarity? -/
def checkFalseNode (ctx : Ctx) (neg : Nat) (e : Expr) (locus : String) : MetaM Unit := do
  if neg > 0 then return ()
  if let some ty ← inferTypeSafe e then
    if ty.isConstOf ``False then
      ctx.fail s!"constructs False in positive position ({locus})"
    else if let .const n _ := ty.getAppFn then
      -- an inhabitant of any constructor-less
      -- inductive (Empty, PEmpty) is a contradiction like `False`
      if let some (.inductInfo iv) := ctx.env.find? n then
        if iv.ctors.isEmpty then
          ctx.fail s!"constructs an inhabitant of the empty type {n} in positive position ({locus})"

/-- A `False` proof manufactured by a non-local `noConfusion`-family constant
whose discriminated equation is a bare case-binder variable is compiled case
analysis killing an impossible branch, not an ex-falso route. The
bare-variable guard matters: an equation derived from the antecedent or from
content lemmas is an application, fails the guard, and keeps the eliminator
convicted; the caller separately requires the argument's type to reduce to
`False`. -/
def benignNoConfusionFalse (ctx : Ctx) (arg : Expr) : MetaM Bool := do
  let .const nc _ := arg.getAppFn | return false
  unless nameHasNoConfusion nc do return false
  if isLocalConst ctx.env nc then return false
  for a in arg.getAppArgs do
    if a.isFVar then
      -- the equation must be a pure case-analysis binder: an antecedent-involved
      -- absurd equation discriminated in positive position is ex-falso
      -- laundering (derive `false = true` from the antecedent, prove anything)
      if (← ctx.anteFVars.get).contains a.fvarId! then continue
      if ← anteInvolved ctx a then continue
      if let some ty ← inferTypeSafe a then
        if (← whnfR ty).isAppOfArity ``Eq 3 then
          return true
  return false

/-- Binding forms: `letFun v (fun h => b)`, beta-redex `(fun h => b) v`, `letE`. -/
structure Binding where
  binderName : Name
  binderType : Expr
  value      : Expr
  mkBody     : Expr → Expr
  binderInfo : BinderInfo := .default
  /-- does the body mention the bound name? (an unused negation binder
  does not switch polarity) -/
  bodyUses   : Bool := true

/-- Recognize a binding form. -/
def asBinding? (e : Expr) : Option Binding :=
  if e.isAppOfArity ``letFun 4 then
    let args := e.getAppArgs
    match args[3]! with
    | .lam n t b bi => some ⟨n, t, args[2]!, fun x => b.instantiate1 x, bi, b.hasLooseBVar 0⟩
    | _ => none
  else match e with
    | .app (.lam n t b bi) v => some ⟨n, t, v, fun x => b.instantiate1 x, bi, b.hasLooseBVar 0⟩
    | .letE n t v b _ => some ⟨n, t, v, fun x => b.instantiate1 x, .default, b.hasLooseBVar 0⟩
    | _ => none

/-- Entering a lambda whose body proves `False` constructs a negation proof,
but only when the binder is used: `by_contra h` with `h` never mentioned is
`False.elim` in disguise and keeps the outer polarity. -/
def negBump (body : Expr) (binderUsed : Bool := true) : MetaM Nat := do
  if !binderUsed then return 0
  match ← inferTypeSafe body with
  | some ty =>
    if ty.isConstOf ``False then return 1
    -- `Bool.noConfusion h : Bool.noConfusionType False false true` is a proof
    -- of `False` after reduction
    let ty' ← try whnfD ty catch _ => pure ty
    return (if ty'.isConstOf ``False then 1 else 0)
  | none => return 0

/-- Heads that collapse a proposition to `True` (or drop a conjunct) on the
strength of a proof of it: inside a rewrite record or a local bridge's
proof, the proof they consume is a goal part closed without the antecedent
when its cone is antecedent-free. -/
def collapseHead (c : Name) : Bool :=
  c == ``eq_true || c == ``iff_of_true || c == ``and_iff_left || c == ``and_iff_right ||
  c == ``iff_true_intro || c == `eq_true_intro || c == ``of_iff_true

/-- Does this record actually rewrite? A justification whose two sides
coincide (`congrArg (fun _ => G) h : G = G`) transports nothing and must not
freeze the converted proof. -/
def recordRewrites (rec : Expr) : MetaM Bool := do
  let some ty ← inferTypeSafe rec | return true
  let ty ← whnfR ty
  let sides : Option (Expr × Expr) :=
    if ty.isAppOfArity ``Eq 3 then some (ty.getArg! 1, ty.getArg! 2)
    else if ty.isAppOfArity ``Iff 2 then some (ty.getArg! 0, ty.getArg! 1)
    else if ty.isAppOfArity ``HEq 4 then some (ty.getArg! 1, ty.getArg! 3)
    else none
  match sides with
  | some (a, b) =>
    if a == b then return false
    return !(← isDefEqCheap a b)
  | none => return true

/-- Role-transition heads: the `.mp`/`.mpr` conversions of Iff and Eq. -/
def transitionHead (c : Name) : Bool :=
  c == ``Iff.mp || c == ``Iff.mpr || c == ``Eq.mp || c == ``Eq.mpr

/-- Simp's goal-conversion wrappers: their argument is a manufactured equation
record, like a transition's record. -/
def recordHead (c : Name) : Bool :=
  c == ``of_eq_true || c == ``of_eq_false

/-- The bare-bridge rule's scope: the conclusion head is literally Eq, Iff or
HEq (no Ne, no class escape). -/
def plainEqIffConcl (env : Environment) (c : Name) : MetaM Bool := do
  let some info := env.find? c | return false
  try
    forallTelescope info.type fun _ concl =>
      pure (match concl.getAppFn with
        | .const h _ => h == ``Eq || h == ``Iff || h == ``HEq
        | _ => false)
  catch _ => return false

/-- Rewrite-substitution eliminators: their major is a transport record. -/
def eqRecFamily (c : Name) : Bool :=
  c == ``Eq.rec || c == ``Eq.ndrec || c == ``Eq.casesOn || c == ``Eq.subst ||
  c == ``HEq.rec || c == ``HEq.ndrec || c == ``Eq.mpr || c == ``Eq.mp

/-- Is this head one whose applications may have a content-free type? Conversion
and wrapper heads, projections, and constants whose conclusion (after its
binders) is an equation, a biconditional, `True`, or a bound variable. -/
def deadTypeCandidate (ctx : Ctx) (f : Expr) : MetaM Bool := do
  match f with
  | .proj .. => return true
  | .const c _ =>
    if transitionHead c || recordHead c || eqRecFamily c || c == ``cast || c == ``Eq.subst
        || c == ``True.intro || c == ``trivial then return true
    let some info := ctx.env.find? c | return false
    let mut t := info.type
    while t.isForall do t := t.bindingBody!
    return t.isConstOf ``True || t.isAppOf ``Eq || t.isAppOf ``Iff || t.isBVar
  | _ => return false

/-- `True`, or a closed equation / biconditional whose sides are syntactically
or (cheaply) definitionally equal. -/
def trivialType (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  if ty.isConstOf ``True then return true
  let sides : Option (Expr × Expr) :=
    if ty.isAppOfArity ``Eq 3 then some (ty.getArg! 1, ty.getArg! 2)
    else if ty.isAppOfArity ``Iff 2 then some (ty.getArg! 0, ty.getArg! 1)
    else none
  let some (a, b) := sides | return false
  if a == b then return true
  if a.hasFVar || b.hasFVar || a.hasLooseBVars || b.hasLooseBVars then return false
  -- the content-free case is small (`decide P` against `true`); large closed
  -- sides (a real-number identity) are not worth a definitional attempt
  if a.approxDepth > 32 || b.approxDepth > 32 then return false
  isDefEqCheap a b

/-- Load-bearing involvement. A mention of the antecedent that cannot carry
its content into the part's conclusion (the discarded argument of
`Function.const` or `id`, a beta-redex's or `have`'s unused binder, an unused
`let`, any conversion or wrapper node whose type is `True`) does not count:
`⟨A, Function.const _ (by decide) A⟩` is a goal part closed without the
antecedent. Memoised on the term, since proof terms from `omega` or
`nlinarith` are DAGs with heavy sharing. Type inference is limited to the
conversion and wrapper heads that produce `True`-typed proofs and to closed
terms (under a binder the node is kept). -/
partial def lbInvolvedGo (ctx : Ctx) (memo : IO.Ref (Std.HashMap Expr Bool)) (e : Expr)
    : MetaM Bool := do
  if let some r := (← memo.get).get? e then return r
  let r ← go e
  memo.modify (·.insert e r)
  return r
where
  go (e : Expr) : MetaM Bool := do
    match e with
    | .bvar _ | .mvar _ | .sort _ | .lit _ => return false
    | .fvar id => return (← ctx.anteFVars.get).contains id
    | .const c _ =>
      if c == ctx.ante then return true
      if isLocalConst ctx.env c then constReaches ctx ctx.reachMemo ctx.ante c else return false
    | .mdata _ b => lbInvolvedGo ctx memo b
    | .proj _ _ b => lbInvolvedGo ctx memo b
    | .forallE _ d b _ => return (← lbInvolvedGo ctx memo d) || (← lbInvolvedGo ctx memo b)
    | .lam _ d b _ => return (← lbInvolvedGo ctx memo d) || (← lbInvolvedGo ctx memo b)
    | .letE _ t v b _ =>
      if !b.hasLooseBVar 0 then lbInvolvedGo ctx memo b
      else return (← lbInvolvedGo ctx memo t) || (← lbInvolvedGo ctx memo v) || (← lbInvolvedGo ctx memo b)
    | .app .. =>
      let e' := e.headBeta
      if e' != e then return ← lbInvolvedGo ctx memo e'
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const c _ := f then
        if c == ``Function.const && args.size ≥ 3 then return ← lbInvolvedGo ctx memo args[2]!
        if c == ``id && args.size ≥ 2 then return ← lbInvolvedGo ctx memo args[1]!
        -- `have _ := v; body` with the name unused
        if c == ``letFun && args.size == 4 then
          if let .lam _ _ b _ := args[3]! then
            if !b.hasLooseBVar 0 then return ← lbInvolvedGo ctx memo b
      -- a node whose type is content-free (`True`, or a closed equation whose
      -- sides are definitionally equal, as `decide P = true` for a closed
      -- decidable `P`) carries nothing forward whatever it is built from
      if !e.hasLooseBVars && (← deadTypeCandidate ctx f) then
        if let some ty ← inferTypeSafe e then
          if ← trivialType ty then return false
      if ← lbInvolvedGo ctx memo f then return true
      for a in args do
        if ← lbInvolvedGo ctx memo a then return true
      return false

/-- Load-bearing involvement (cheap syntactic pre-check first). -/
def anteInvolvedLB (ctx : Ctx) (e : Expr) : MetaM Bool := do
  if !(← anteInvolved ctx e) then return false
  let memo ← IO.mkRef ({} : Std.HashMap Expr Bool)
  lbInvolvedGo ctx memo e

/-- Extensionality introductions whose lambda binders inherit pair-aligned
surface status (budgeted), symmetric to the destructuring-products rule:
`funext`'s pointwise variable is the honest way a proof reaches inside an
extensional goal. -/
def extIntroHead (c : Name) : Bool :=
  c == ``funext || c == ``propext || c == ``Subtype.ext ||
  -- Mathlib names (not importable here; matched against the fixture env)
  c == `Set.ext || c == `SetLike.ext || c == `Finset.ext

/-- The head is a projection function (a structure or class field accessor:
`And.right`, `Iff.mp`, `Fact.out`) whose record argument is
antecedent-involved: the application consumes an antecedent-derived fact, so
the arguments after the major feed the antecedent pipeline. -/
def projConsumerAnte (ctx : Ctx) (c : Name) (args : Array Expr)
    : MetaM (Option Nat) := do
  let some pi := ctx.env.getProjectionFnInfo? c | return none
  if pi.numParams < args.size then
    let major := args[pi.numParams]!
    if (← isProofSafe major) && (← anteInvolved ctx major) then
      return some pi.numParams
  return none

/-- Slot kinds of the antecedent's syntactic telescope: `true` = data (non-Prop). -/
def anteSlotKinds (ty : Expr) : MetaM (Array Bool) :=
  forallTelescope ty fun xs _ => xs.mapM fun x => do
    let t ← inferType x
    pure !(← try Meta.isProp t catch _ => pure true)

/-- Pair-aligned surface data depth of the goal: the data binders of the
goal's syntactic telescope, extended by unfolding its conclusion while the
antecedent's data surface is deeper, so the boundary is set by the depth at
which the pair speaks, not by either statement's presentation alone. Prop
binders neither count nor consume: by proof irrelevance they cannot change
which statement an antecedent instance asserts. -/
partial def extendedSurfaceDataArity (ty : Expr) (target : Nat) : MetaM Nat := do
  forallTelescope ty fun xs concl => do
    let mut n := 0
    for x in xs do
      let t ← inferType x
      if !(← try Meta.isProp t catch _ => pure true) then n := n + 1
    if n ≥ target then return n
    let c ← try whnf concl catch _ => pure concl
    if c.isForall then
      return n + (← extendedSurfaceDataArity c (target - n))
    -- the goal's own binders may sit inside its propositional
    -- structure (`(∀ n, …) ∧ (∀ n, …)`, `∃ x, ∀ n, …`)
    else if c.isAppOfArity ``And 2 || c.isAppOfArity ``Iff 2 then
      let a ← extendedSurfaceDataArity (c.getArg! 0) (target - n)
      let b ← extendedSurfaceDataArity (c.getArg! 1) (target - n)
      return n + a + b
    else if c.isAppOfArity ``Exists 2 then
      match c.getArg! 1 with
      | .lam .. => lambdaTelescope (c.getArg! 1) fun _ body => do
          return n + (← extendedSurfaceDataArity body (target - n))
      | _ => return n
    else return n

/-- The first data fvar in `a`'s closure lying outside the established
surface. Prop fvars are exempt everywhere, since by proof irrelevance they
cannot change which statement an antecedent instance asserts. -/
def surfaceViolation? (ctx : Ctx) (a : Expr) : MetaM (Option FVarId) := do
  let surface ← ctx.surfaceFVars.get
  for fv in (Lean.collectFVars {} a).fvarIds do
    unless surface.contains fv do
      if let some d ← fv.findDecl? then
        let isPf ← try Meta.isProp d.type catch _ => pure true
        if !isPf then return some fv
  return none

/-- Resolve a let- or have-bound fvar to its recorded value (transitively), so
the carrier rules judge the construction, not the name. -/
partial def resolveLocal (ctx : Ctx) (e : Expr) : MetaM Expr := do
  if e.isFVar then
    if let some v := (← ctx.localValues.get).get? e.fvarId! then
      return ← resolveLocal ctx v
  return e

/-- Does the goal's own (opened) statement mention `e`? The audits' standard
is that the antecedent must be used at the objects the pair's statements
speak about, and the goal's statement type is the ground truth of what it
speaks about. -/
def occursInGoalStmt (ctx : Ctx) (e : Expr) : MetaM Bool := do
  let parts := (← ctx.goalOpenParts.get).push (← ctx.goalTypeRem.get)
  return parts.any fun p => (p.find? (· == e)).isSome

/-- The propositions on the goal statement's propositional spine: the
statement itself and everything reachable through ∧, ↔, ∨ and ¬, the body of
a ∀ or → and the body of an ∃. A proposition inside a term (an `if`
condition, a set-builder body) is not a goal part; collapsing it to `True`
reduces the goal, it does not prove a part of it. Parts under a remaining
binder keep their loose bvars, which `matchWild` treats as wildcards. -/
partial def spineParts (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := acc.push e
  match e with
  | .mdata _ b => spineParts b acc
  | .forallE _ _ b _ => spineParts b acc
  | _ =>
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Iff 2 || e.isAppOfArity ``Or 2 then
      spineParts (e.getArg! 1) (spineParts (e.getArg! 0) acc)
    else if e.isAppOfArity ``Not 1 then spineParts (e.getArg! 0) acc
    else if e.isAppOfArity ``Exists 2 then
      match e.getArg! 1 with
      | .lam _ _ b _ => spineParts b acc
      | _ => acc
    else acc

/-- Structural match in which a loose bound variable of the pattern matches
anything (the goal's not-yet-introduced binders). -/
partial def matchWild (pat e : Expr) : Bool :=
  match pat, e with
  | .bvar _, _ => true
  | .mdata _ p, _ => matchWild p e
  | _, .mdata _ b => matchWild pat b
  | .app pf pa, .app f a => matchWild pf f && matchWild pa a
  | .lam _ pt pb _, .lam _ t b _ => matchWild pt t && matchWild pb b
  | .forallE _ pt pb _, .forallE _ t b _ => matchWild pt t && matchWild pb b
  | .letE _ pt pv pb _, .letE _ t v b _ => matchWild pt t && matchWild pv v && matchWild pb b
  | .proj s i p, .proj s' i' b => s == s' && i == i' && matchWild p b
  | _, _ => pat == e

/-- Is `p` a proposition on the goal's spine (opened with the walk's fvars so
far)? Closed parts are also compared up to definitional unfolding. -/
def spinePropOf (stmt p : Expr) : MetaM Bool := do
  for q in spineParts stmt do
    if matchWild q p then return true
    if !q.hasLooseBVars then
      if ← isDefEqCheap q p then return true
  return false

/-- Is `p` on the spine of the goal's remaining conclusion? -/
def isGoalSpineProp (ctx : Ctx) (p : Expr) : MetaM Bool := do
  -- the remaining conclusion only: the goal's hypotheses (the peeled binders'
  -- types) are premises, not parts to be proved
  spinePropOf (← ctx.goalTypeRem.get) p

/-- Nesting depth of a leading `∃ x y …` (0 for a non-existential). -/
partial def existsDepth : Expr → Nat
  | .mdata _ b => existsDepth b
  | e =>
    if e.isAppOfArity ``Exists 2 then
      match e.getArg! 1 with
      | .lam _ _ b _ => existsDepth b + 1
      | _ => 1
    else 0

/-- A numeral, read literally (`OfNat.ofNat _ n _` or a raw `Nat` literal). -/
def numLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- Look through goal conversions / casts / `id` to the term itself. -/
partial def stripCasts : Expr → Expr
  | .mdata _ b => stripCasts b
  | e =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
      if (c == ``Eq.mpr || c == ``Eq.mp || c == ``cast) && args.size == 4 then stripCasts args[3]!
      else if c == ``id && args.size == 2 then stripCasts args[1]!
      else e
    | _ => e

/-- Closed-witness audit. The antecedent's existential hypothesis
`∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)` met with the witness `0`, a closed term the
proof conjures, while the goal's own hypothesis `h : ∃ i : ℤ, …` already
supplies the corresponding object, is not an honest transport, which would
witness with a term built from `i`. At an application of the antecedent,
every argument in an existential-hypothesis slot that is an `Exists.intro`
(possibly under casts, or a `have`-bound name whose value is one) has its
witnesses examined, nested `∃`s included. A witness with no free variable of
the proof context (let-bound names resolved to their values first) that does
not occur in the goal statement (numerals compared literally) refuses the
proof; so does a witness built only from antecedent-derived variables (the
walker's taint set). A witness mentioning a goal-side variable (a goal
parameter, a conclusion intro, a product of casing a goal hypothesis), or a
closed term the goal statement mentions, passes.
`SEMANTEQ_NO_WITNESS_CHECK=1` disables the audit. -/
def witnessAudit (ctx : Ctx) (anteType : Expr) (args : Array Expr) : MetaM Unit := do
  let occursInGoal (w : Expr) : Bool :=
    match numLit? w with
    | some n => (ctx.goalStmt.find? (fun e => numLit? e == some n)).isSome
    | none => (ctx.goalStmt.find? (· == w)).isSome
  -- resolve a `have`-bound hypothesis to its proof term (transitively)
  let rec resolveProp (e : Expr) (fuel : Nat) : MetaM Expr := do
    match fuel, e with
    | fuel+1, .fvar id =>
      match (← ctx.propValues.get).get? id with
      | some v => resolveProp v fuel
      | none => pure e
    | _, _ => pure e
  let mut ty := anteType
  for i in [0:args.size] do
    let a := args[i]!
    let ty' ← if ty.isForall then pure ty else (try whnf ty catch _ => pure ty)
    let .forallE _ d body _ := ty' | break
    ty := body.instantiate1 a
    let d ← instantiateMVars d
    let depth := existsDepth d
    if depth == 0 then continue
    -- walk the nested `Exists.intro` chain of the supplied proof
    let mut pf ← resolveProp a 8
    let mut witnesses : Array Expr := #[]
    for _ in [0:depth] do
      pf := stripCasts pf
      pf ← resolveProp pf 8
      if pf.isAppOfArity ``Exists.intro 4 then
        witnesses := witnesses.push (pf.getArg! 2)
        pf := pf.getArg! 3
      else break
    for w in witnesses do
      -- let-bound names are read as their values (transitively), so a witness
      -- `n` with `let n := 0` is the closed term `0`, not a variable
      let w ← instantiateMVars (← resolveLocal ctx w)
      if w.hasMVar then continue
      -- built from the goal means mentioning a goal-side variable: any free
      -- variable of the proof context that is not tainted (`anteFVars`:
      -- bindings with antecedent-involved values and the products of
      -- destructuring antecedent-derived facts)
      let tainted ← ctx.anteFVars.get
      let fvs := (Lean.collectFVars {} w).fvarIds
      -- `SEMANTEQ_AUDIT_TRACE`: every examined witness and what became of it
      let census (kind : String) : MetaM Unit := do
        if ← auditTrace then
          IO.eprintln s!"[trace] witness {kind} (slot {i}): {← Meta.ppExpr w}"
      if fvs.any (fun fv => !tainted.contains fv) then
        census "built from a goal-side variable, admitted"
        continue
      if fvs.isEmpty then
        if occursInGoal w then
          census "closed, occurs in the goal statement, admitted"
          continue
        census "closed, foreign to the goal statement, refused"
        ctx.fail s!"antecedent existential hypothesis met with a closed witness foreign to the goal statement: {← Meta.ppExpr w} (slot {i})"
      else
        census "built only from antecedent-derived variables, refused"
        ctx.fail s!"antecedent existential hypothesis met with a witness built only from antecedent-derived variables, not from the goal: {← Meta.ppExpr w} (slot {i})"

/-- The severe tier of the antecedent-argument warning. Traverse `e`, looking
through have- and let-bound locals, and report whether it draws on a local
proposition and whether it mentions a local variable at all. A local
proposition is a valueless Prop-typed fvar (a hypothesis), an
antecedent-involved fvar, the antecedent itself, or an environment-local
constant that reaches the antecedent. -/
partial def localityGo (ctx : Ctx) (seen : IO.Ref FVarIdSet)
    (prop data : IO.Ref Bool) : Expr → MetaM Unit
  | .fvar id => do
    if (← seen.get).contains id then return ()
    seen.modify (·.insert id)
    if (← ctx.anteFVars.get).contains id then prop.set true
    if let some v := (← ctx.propValues.get).get? id then localityGo ctx seen prop data v
    else if let some v := (← ctx.localValues.get).get? id then localityGo ctx seen prop data v
    else
      data.set true
      if let some ty ← inferTypeSafe (mkFVar id) then
        if ← (isPropSafe ty) then prop.set true
  | .const c _ => do
    if c == ctx.ante then prop.set true
    else if isLocalConst ctx.env c then
      if ← constReaches ctx ctx.reachMemo ctx.ante c then prop.set true
  | .app f a => do localityGo ctx seen prop data f; localityGo ctx seen prop data a
  | .lam _ t b _ => do localityGo ctx seen prop data t; localityGo ctx seen prop data b
  | .forallE _ t b _ => do localityGo ctx seen prop data t; localityGo ctx seen prop data b
  | .letE _ t v b _ => do
    localityGo ctx seen prop data t; localityGo ctx seen prop data v; localityGo ctx seen prop data b
  | .mdata _ b => localityGo ctx seen prop data b
  | .proj _ _ b => localityGo ctx seen prop data b
  | _ => pure ()

/-- (draws on a local proposition, mentions a local variable); see `localityGo`. -/
def localityOf (ctx : Ctx) (e : Expr) : MetaM (Bool × Bool) := do
  let seen ← IO.mkRef ({} : FVarIdSet)
  let prop ← IO.mkRef false
  let data ← IO.mkRef false
  localityGo ctx seen prop data e
  return (← prop.get, ← data.get)

/-- Inside a rewrite record or a local bridge's proof, positional goal-part
ablations are suspended (the sub-proof proves the record or the bridge, not
the goal); only the collapse rules convict there. -/
def ablationSuspended (ctx : Ctx) : MetaM Bool := do
  return (← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0

/-- Inside a record or a local bridge's proof, an antecedent-free proof of
`p = True` or `p ↔ True` for a goal spine part `p` is a goal part closed
without the antecedent, whatever head built it (`if_pos`, `decide_eq_true`,
a `_simp_N` auxiliary, `propext …`). -/
def checkCollapseEquation (ctx : Ctx) (e ty : Expr) : MetaM Unit := do
  let ty ← instantiateMVars ty
  let p? : Option Expr :=
    if ty.isAppOfArity ``Eq 3 then
      if (ty.getArg! 2).isConstOf ``True then some (ty.getArg! 1)
      else if (ty.getArg! 1).isConstOf ``True then some (ty.getArg! 2) else none
    else if ty.isAppOfArity ``Iff 2 then
      if (ty.getArg! 1).isConstOf ``True then some (ty.getArg! 0)
      else if (ty.getArg! 0).isConstOf ``True then some (ty.getArg! 1) else none
    else none
  let some p := p? | return ()
  if p.isConstOf ``True then return ()
  if ← anteInvolved ctx p then return ()
  unless ← isGoalSpineProp ctx p do return ()
  if ← anteInvolvedLB ctx e then return ()
  ctx.fail s!"goal part closes ante-free (equated to True inside a rewrite record or a local bridge's proof: {← Meta.ppExpr p})"

/-- If judging the head `c` just raised an antecedent-argument content
warning, add the severe tier when the whole application draws on no local
proposition. -/
def severeIfClosed (ctx : Ctx) (nBefore : Nat) (c : Name) (args : Array Expr) : MetaM Unit := do
  let flags ← ctx.flags.get
  let fresh := flags.extract nBefore flags.size
  unless fresh.any (fun s => (s.splitOn "feeding ante application").length > 1) do return ()
  let (prop, data) ← localityOf ctx (mkAppN (.const c []) args)
  unless prop do
    let note := if data then "" else ", nor on any local variable"
    ctx.severe s!"outside fact {c} feeding ante application draws on no local hypothesis{note}"
end ProofAudit
end SemantEq
