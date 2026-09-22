import SemantEq.Compile
import SemantEq.Statement
import SemantEq.Search
import SemantEq.Env

/-!
# Faithful proof checker — `semanteq --proof <fixture>`

Audits a model-written (or hand-written) implication proof for faithfulness.
The fixture rules:

* #1 eliminator dispatch precedes the bridge arm (Prop-motive eliminators no
  longer demote case splits to SIDE),
* #2 eliminators keyed semantically (recursor kind / motive-headed conclusion),
  `schematicType` closed over core-logic namespaces,
* #3 sorried in-file theorems = OUTSIDE lemmas with licensed sorry (statement
  graded × role; strict parity — they never rescue a part from "closes ante-free"),
* #4 proven in-file lemmas get the have-Prop asymmetry: ante-free → statement
  graded, proof closed; ante-involved → sanctioned statement, proof expanded,
* #5 goal-shaped local bridges are flagged.

Verdict per fixture: PASS(flags) / FAIL(reasons) / SKIP_SORRY / ERROR, as JSONL.
-/

namespace SemantEq
namespace ProofAudit

open Lean Elab Meta

/-- Reject-dominant role lattice: GOAL > ANTE-ARG > SIDE. -/
inductive Role | goal | anteArg | side
deriving BEq, Repr, Inhabited

def Role.join : Role → Role → Role
  | .goal, _ => .goal
  | _, .goal => .goal
  | .anteArg, _ => .anteArg
  | _, .anteArg => .anteArg
  | _, _ => .side

def Role.str : Role → String
  | .goal => "GOAL" | .anteArg => "ANTE-ARG" | .side => "SIDE"

/-- Core logical vocabulary for the schematic test. A constant whose TYPE is built
solely from sorts, variables, and these heads is a tautology schema — it cannot
carry domain content. Replaces the legacy name whitelist
: supersedes `RestrictedSearch.structuralWhitelist`). -/
def coreLogic : NameSet := .ofList
  [``Eq, ``HEq, ``Iff, ``And, ``Or, ``Not, ``Ne, ``Exists, ``True, ``False]

/-- the namespace closure — `Exists.intro`, `Or.inl`, `And.casesOn`, …
belong to core logic by their root, so eliminator/constructor mentions inside a
core-logic constant's own type do not break schematicity. -/
def coreLogicName (c : Name) : Bool :=
  coreLogic.contains c || coreLogic.contains c.getRoot

/-- The one retained name list: eliminators of `False`
: mirrors `RestrictedSearch.exFalsoConstants`). -/
def exFalso5 : NameSet := .ofList
  [``False.elim, ``False.rec, ``False.casesOn, ``absurd, ``Not.elim]

/-- Ledger 30(i): heads of the `noConfusion` family (auto-generated
discriminators, `noConfusion_of_Nat`-style helpers). -/
def nameHasNoConfusion (c : Name) : Bool :=
  ((toString c).splitOn "noConfusion").length > 1

/-- Conclusion heads accepted as bridge-grade
: mirrors `RestrictedSearch.acceptedHeads`). -/
def acceptedHeads : List Name := [``Eq, ``Iff, ``HEq, ``Ne]

/-- Is this TYPE a pure logical schema? Allowed: sorts, bound/free variables,
Pi/lambda, and applications headed by a variable or a core-logic constant
(namespace-closed, the namespace-closure rule). -/
partial def schematicType : Expr → Bool
  | .sort _ => true
  | .bvar _ => true
  | .fvar _ => true
  | .mdata _ b => schematicType b
  | .forallE _ d b _ => schematicType d && schematicType b
  | .lam _ d b _ => schematicType d && schematicType b
  | .const c _ => coreLogicName c
  | e@(.app ..) =>
    let f := e.getAppFn
    let headOk := match f with
      | .bvar _ => true
      | .fvar _ => true
      | .const c _ => coreLogicName c
      | _ => false
    headOk && e.getAppArgs.all schematicType
  | _ => false

inductive Cat
  | sanctioned | sorryC | exFalso | data | schematic | bridge | content
deriving BEq, Repr

structure Ctx where
  env        : Environment
  ante       : Name
  /-- OTHER sorried in-file theorems — outside lemmas with a licensed
  sorry. Never sanctioned, never expanded, never rescue a part from ablation. -/
  assumed    : NameSet := {}
  catMemo    : IO.Ref (NameMap Cat)
  reachMemo  : IO.Ref (NameMap Bool)      -- env-local const → reaches ante?
  sorryMemo  : IO.Ref (NameMap Bool)      -- env-local const → reaches sorryAx?
  localGrade : IO.Ref (NameMap Bool)      -- assumed/ante-free-local: bridge-graded?
  goalParts  : IO.Ref (Array Expr)        -- ∧-split goal conclusion
  /-- Carrier-affinity audit : every constant of the goal
  statement's type, plus whether `Prop` itself appears as a binder-domain
  carrier there. An ante application instantiating a type parameter whose
  vocabulary is disjoint from this set is off-subject. -/
  goalConsts : NameSet := {}
  goalPropCarrier : Bool := false
  /-- The goal's conclusion existentially quantifies a Sort — its type witness
  is arbitrary by nature, so foreign carriers are legitimate there. -/
  goalSortExists : Bool := false
  /-- refinement: does the goal STATEMENT's telescope bind a finiteness
  instance (Finite/Fintype)? Distinguishes the honest Finite→Fintype upgrade
  (goal grants finiteness) from a manufactured mint (0459: finiteness built
  from vacuous Prop hypotheses, not a goal binder). Computed from goalType so a
  `have`-minted Finite in the proof body cannot spoof it. -/
  goalHasFin : Bool := false
  occRoles   : IO.Ref (FVarIdMap Role)
  anteFVars  : IO.Ref FVarIdSet
  /-- (data-surface instantiation audit): fvars established as the
  pair-aligned statement surface — goal-telescope binders up to the aligned
  depth, surface-valued data bindings, and destructuring products of
  surface-rooted eliminations. -/
  surfaceFVars : IO.Ref FVarIdSet
  /-- countdown of goal-proof leading lambdas still to mark as surface -/
  surfaceLeft : IO.Ref Nat
  /-- kinds of the ante's syntactic telescope binders: true = data (non-Prop) -/
  anteSlotData : IO.Ref (Array Bool)
  /-- the goal's statement, opened progressively with the walk's
  own fvars — binder domains already peeled, plus the remainder — so a
  carrier argument can be tested for occurrence in what the goal itself
  says (`↥F` inside `IsAlgebraic F a`). -/
  goalOpenParts : IO.Ref (Array Expr)
  goalTypeRem : IO.Ref Expr
  /-- census v2: transport-context depth (flag-only diagnostics) -/
  chainCtx : IO.Ref Nat
  /-- values of local data bindings (handleBinding introduces
  binding fvars valueless via withLocalDecl; the carrier rules must resolve
  a let-bound name to its value before the bare-surface test, or a
  `let X := <construction>` would launder past l.36/37) -/
  localValues : IO.Ref (FVarIdMap Expr)
  /-- severe-warning tier: values of local Prop bindings (`have`), so a use of
  an outside fact can be tested for whether it draws on any local hypothesis
  through such a binding -/
  propValues : IO.Ref (FVarIdMap Expr)
  fails      : IO.Ref (Array String)
  flags      : IO.Ref (Array String)
  sorryHit   : IO.Ref Bool
  expanded   : IO.Ref NameSet             -- env-local consts already judged-through

def Ctx.fail (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.fails.modify (·.push r)

def Ctx.flag (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.flags.modify (·.push r)

/-- Constant value with kernel-env fallback; 4.30 hides theorem values behind
`allowOpaque` : discipline of `RestrictedSearch.auditProof`). -/
def valueOf? (env : Environment) (c : Name) : Option Expr := do
  let info ← env.toKernelEnv.find? c <|> env.find? c
  info.value? (allowOpaque := true)

def isLocal (env : Environment) (c : Name) : Bool :=
  (env.getModuleIdxFor? c).isNone

/-- Does env-local constant `c` reach `target` through env-local values? Never
looks inside the ante or the assumed set (their sorries are licensed; they also
must not launder reachability). : mirrors `Search.usesConstant`.) -/
partial def constReaches (ctx : Ctx) (memo : IO.Ref (NameMap Bool))
    (target : Name) (c : Name) : MetaM Bool := do
  if let some b := (← memo.get).find? c then return b
  memo.modify (·.insert c false)  -- provisional false cuts cycles
  let mut out := false
  if c == target then
    out := true
  else if c == ctx.ante || ctx.assumed.contains c then
    out := false
  else if isLocal ctx.env c then
    if let some v := valueOf? ctx.env c then
      for c' in v.getUsedConstantsAsSet do
        if c' == target then out := true
        else if c' != ctx.ante && !ctx.assumed.contains c' && isLocal ctx.env c' then
          if ← constReaches ctx memo target c' then out := true
  memo.modify (·.insert c out)
  return out

/-- Does `e` involve the antecedent (constant mention, env-local reach, or an
ante-involved local hypothesis)? Strict parity: assumed theorems do NOT count. -/
def anteInvolved (ctx : Ctx) (e : Expr) : MetaM Bool := do
  let fvs ← ctx.anteFVars.get
  if e.hasAnyFVar (fvs.contains ·) then return true
  for c in e.getUsedConstantsAsSet do
    if c == ctx.ante then return true
    if isLocal ctx.env c then
      if ← constReaches ctx ctx.reachMemo ctx.ante c then return true
  return false

/-- Does `e` reach `sorryAx` other than through the ante/assumed set? -/
def reachesSorry (ctx : Ctx) (e : Expr) : MetaM Bool := do
  for c in e.getUsedConstantsAsSet do
    if c == ``sorryAx then return true
    if c != ctx.ante && !ctx.assumed.contains c && isLocal ctx.env c then
      if ← constReaches ctx ctx.sorryMemo ``sorryAx c then return true
  return false

def isProofSafe (e : Expr) : MetaM Bool := do
  try Meta.isProof e catch _ => return false

def inferTypeSafe (e : Expr) : MetaM (Option Expr) := do
  try return some (← inferType e) catch _ => return none

/-- Grade a STATEMENT expression: bridge-grade iff its conclusion head is
Eq/Iff/HEq/Ne, a class, a variable, or the whole statement is schematic. -/
def bridgeGradeType (env : Environment) (t : Expr) : MetaM Bool := do
  if schematicType t then return true
  -- plain head FIRST (pattern: `Ne` unfolds to `→ False` under a reducing
  -- telescope, which would strip Ne-stated local bridges of their grade)
  let plain ← try
    forallTelescope t fun _ concl =>
      pure (match concl.getAppFn with
        | .const h _ => acceptedHeads.contains h
        | .fvar _ => true
        | .bvar _ => true
        | _ => false)
    catch _ => pure false
  if plain then return true
  try
    forallTelescopeReducing t fun _ concl => do
      match concl.getAppFn with
      | .const h _ =>
        if acceptedHeads.contains h || Lean.isClass env h then return true
        -- abbrev-wrapped class conclusions (same FP as auditProof,)
        return (← Meta.isClass? concl).isSome
      | .fvar _ => return true
      | .bvar _ => return true
      | _ => return false
  catch _ => return false

/-- Case-split-style name suffixes (heuristic half of the eliminator test). -/
def elimSuffix (c : Name) : Bool :=
  match c with
  | .str _ s => s == "casesOn" || s == "rec" || s == "recOn"
      || s == "elim" || s == "byCases"
  | _ => false

/-- a genuine eliminator — a real recursor, or an elim-suffix-named
constant whose PLAIN conclusion is variable-headed (a motive). A bridge lemma
that merely happens to be named `*.elim` (Eq/Iff-headed conclusion) is excluded. -/
def isEliminatorConst (env : Environment) (c : Name) : MetaM Bool := do
  match env.find? c with
  | some (.recInfo _) => return true
  | some info =>
    if !elimSuffix c then return false
    try
      forallTelescope info.type fun _ concl =>
        pure concl.getAppFn.isFVar
    catch _ => return false
  | none => return false

/-- Category of a GLOBAL constant (memoized). Env-local constants are handled by
family (`judgeOutsideLocal` / `expandLocal`), never here. -/
def categorize (ctx : Ctx) (c : Name) : MetaM Cat := do
  if c == ctx.ante then return .sanctioned
  if c == ``sorryAx then return .sorryC
  if exFalso5.contains c then return .exFalso
  if let some cat := (← ctx.catMemo.get).find? c then return cat
  let cat ← do
    -- eliminators are never bridge — their motive-headed conclusions
    -- were sailing through the `.fvar => true` case below
    if ← isEliminatorConst ctx.env c then pure Cat.schematic
    else
    match ctx.env.find? c with
    | none => pure Cat.data
    | some info => do
      if !(← try Meta.isProp info.type catch _ => pure false) then
        pure Cat.data                     -- defs, structures, instances, recursors
      else if schematicType info.type then
        pure Cat.schematic
      else
        -- plain head first, then reducing : pattern in
        -- `RestrictedSearch.auditProof` / `eqIffConclusioned`)
        let plain ← try
          forallTelescope info.type fun _ concl =>
            pure (match concl.getAppFn with
              | .const h _ => acceptedHeads.contains h
              | .fvar _ => true
              | _ => false)
          catch _ => pure false
        if plain then pure Cat.bridge
        else
          let red ← try
            forallTelescopeReducing info.type fun _ concl => do
              match concl.getAppFn with
              | .const h _ =>
                if acceptedHeads.contains h || Lean.isClass ctx.env h then return true
                return (← Meta.isClass? concl).isSome
              | .fvar _ => return true
              | _ => return false
            catch _ => pure false
          if red then pure Cat.bridge else pure Cat.content
  ctx.catMemo.modify (·.insert c cat)
  return cat

def recordOcc (ctx : Ctx) (id : FVarId) (role : Role) : MetaM Unit :=
  ctx.occRoles.modify fun m =>
    m.insert id ((m.get? id).map (Role.join role) |>.getD role)

/-- Carrier-affinity audit :
an ante application that instantiates a `Sort`-valued parameter at a carrier
sharing NOTHING with the goal statement — no free variable of the proof
context, no constant of the goal's type — is using the ante off-subject as a
generic schema while the real content arrives through its value arguments
(ANTE-ARG, where content only flags). Native carriers (the goal's own types,
subtypes/products/images built from them) all share vocabulary and pass. -/
def foreignCarrier (ctx : Ctx) (t : Expr) : Bool :=
  if t.hasFVar then false          -- anchored to something in scope
  else if t.isSort then !ctx.goalPropCarrier  -- bare Prop/Sort instantiation
  else
    t.getUsedConstantsAsSet.all fun c =>
      coreLogicName c || !ctx.goalConsts.contains c

/-- `SEMANTEQ_AUDIT_TRACE`: log every constant grading decision. -/
def auditTrace : IO Bool := do
  return (← envVar "AUDIT_TRACE").isSome
/-- Judge one global constant under a role and polarity — the decision table. -/
def judgeConst (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (locus : String)
    : MetaM Unit := do
  if ← auditTrace then
    let cat ← categorize ctx c
    if cat == .content then
      IO.eprintln s!"[trace] content {c} @ {role.str} ({locus})"
  match ← categorize ctx c with
  | .sorryC => ctx.sorryHit.set true
  | .exFalso =>
    if neg == 0 then
      ctx.fail s!"ex-falso eliminator {c} in positive position ({locus})"
  | .content =>
    match role with
    | .goal => ctx.fail s!"content import {c} on goal spine ({locus})"
    | .anteArg => ctx.flag s!"content import {c} feeding ante application ({locus})"
    | .side => pure ()
  | _ => pure ()

/-- do the Iff/Eq sides of this statement unify with a goal part?
Over-eager matches (metavariable-assisted) are acceptable — this only flags. -/
def goalShaped (ctx : Ctx) (t : Expr) : MetaM Bool := do
  let parts ← ctx.goalParts.get
  if parts.isEmpty then return false
  try
    let (_, _, concl) ← forallMetaTelescope t
    let sides : Array Expr :=
      match concl.getAppFn.constName? with
      | some n =>
        if (n == ``Iff || n == ``Eq || n == ``HEq) && concl.getAppArgs.size ≥ 2 then
          let a := concl.getAppArgs
          #[a[a.size-2]!, a[a.size-1]!]
        else #[]
      | none => #[]
    for s in sides do
      for p in parts do
        if ← withoutModifyingState (try isDefEq s p catch _ => pure false) then
          return true
    return false
  catch _ => return false

/-- an ante-free in-file lemma or a sorried assumption is an
OUTSIDE lemma — statement graded at the use role, proof closed (sorry licensed
for the assumed). Bridge-graded statements get the goal-shaped check (#5). -/
def judgeOutsideLocal (ctx : Ctx) (role : Role) (c : Name) : MetaM Unit := do
  let some info := ctx.env.find? c | return ()
  -- local VOCABULARY (defs, predicates, structures — non-Prop-typed) is data:
  -- same exemption as the global non-Prop rule (`Nat.Coprime`-style)
  unless ← (try Meta.isProp info.type catch _ => pure false) do
    return ()
  let grade ← do
    if let some g := (← ctx.localGrade.get).find? c then pure g
    else do
      let g ← bridgeGradeType ctx.env info.type
      if g then
        if ← goalShaped ctx info.type then
          ctx.flag s!"goal-shaped local bridge {c}"
      ctx.localGrade.modify (·.insert c g)
      pure g
  unless grade do
    match role with
    | .goal => ctx.fail s!"content-graded local fact {c} on goal spine"
    | .anteArg => ctx.flag s!"content-graded local fact {c} feeding ante application"
    | .side => pure ()

/-- Look through an env-local INTERNAL auxiliary or ante-involved helper: judge
every constant its value uses at the current role. Ante-free user-named lemmas
encountered inside are graded (#4), not expanded.
: expansion discipline of `RestrictedSearch.auditProof`.) -/
partial def expandLocal (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) : MetaM Unit := do
  if ← auditTrace then IO.eprintln s!"[trace] expandLocal {c} @ {role.str} (seen={(← ctx.expanded.get).contains c})"
  if (← ctx.expanded.get).contains c then return ()
  ctx.expanded.modify (·.insert c)
  if let some v := valueOf? ctx.env c then
    for c' in v.getUsedConstantsAsSet do
      if c' == ctx.ante then continue
      if ctx.assumed.contains c' then judgeOutsideLocal ctx role c'
      else if isLocal ctx.env c' then
        if !c'.isInternalDetail && !(← constReaches ctx ctx.reachMemo ctx.ante c') then
          judgeOutsideLocal ctx role c'
        else expandLocal ctx role neg c'
      else judgeConst ctx role neg c' s!"via local {c}"

/-- `False` constructed at positive polarity?
: node test of `RestrictedSearch.constructsFalse?`.) -/
def checkFalseNode (ctx : Ctx) (neg : Nat) (e : Expr) (locus : String) : MetaM Unit := do
  if neg > 0 then return ()
  if let some ty ← inferTypeSafe e then
    if ty.isConstOf ``False then
      ctx.fail s!"constructs False in positive position ({locus})"

/-- Ledger 30(i): a `False` proof manufactured by a non-local
`noConfusion`-family constant whose discriminated equation is a BARE
case-binder variable is compiled case analysis killing an impossible branch —
not an ex-falso route. The bare-variable guard is load-bearing: an equation
DERIVED from the antecedent or from content lemmas (the relocated-content
shape) is an application, fails the guard, and keeps the eliminator
convicted; the caller separately requires the argument's type to whnf-reduce
to `False`, which certifies the discrimination is computationally absurd. -/
def benignNoConfusionFalse (ctx : Ctx) (arg : Expr) : MetaM Bool := do
  let .const nc _ := arg.getAppFn | return false
  unless nameHasNoConfusion nc do return false
  if isLocal ctx.env nc then return false
  for a in arg.getAppArgs do
    if a.isFVar then
      -- the equation must be a pure case-analysis binder: an ANTE-INVOLVED
      -- absurd equation discriminated in positive position is ex-falso
      -- laundering (derive `false = true` from the ante, prove anything)
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

def asBinding? (e : Expr) : Option Binding :=
  if e.isAppOfArity ``letFun 4 then
    let args := e.getAppArgs
    match args[3]! with
    | .lam n t b bi => some ⟨n, t, args[2]!, fun x => b.instantiate1 x, bi⟩
    | _ => none
  else match e with
    | .app (.lam n t b bi) v => some ⟨n, t, v, fun x => b.instantiate1 x, bi⟩
    | .letE n t v b _ => some ⟨n, t, v, fun x => b.instantiate1 x, .default⟩
    | _ => none

/-- Entering a lambda whose body proves `False` = constructing a negation proof. -/
def negBump (body : Expr) : MetaM Nat := do
  match ← inferTypeSafe body with
  | some ty => return (if ty.isConstOf ``False then 1 else 0)
  | none => return 0

/-- Role-transition heads : `.mp`/`.mpr` conversions of the
two bridge structures. Categorical: the transition projections of Iff and Eq. -/
def transitionHead (c : Name) : Bool :=
  c == ``Iff.mp || c == ``Iff.mpr || c == ``Eq.mp || c == ``Eq.mpr

/-- Simp's goal-conversion wrappers: their argument is a manufactured equation
RECORD (ancillary as a whole), like a transition's record. -/
def recordHead (c : Name) : Bool :=
  c == ``of_eq_true || c == ``of_eq_false

/-- Census v2 (the bare-bridge rule, plain-Eq/Iff scope): conclusion head
is literally Eq/Iff/HEq — no Ne, no class escape. -/
def plainEqIffConcl (env : Environment) (c : Name) : MetaM Bool := do
  let some info := env.find? c | return false
  try
    forallTelescope info.type fun _ concl =>
      pure (match concl.getAppFn with
        | .const h _ => h == ``Eq || h == ``Iff || h == ``HEq
        | _ => false)
  catch _ => return false

/-- Rewrite-substitution eliminators: their major IS a transport record. -/
def eqRecFamily (c : Name) : Bool :=
  c == ``Eq.rec || c == ``Eq.ndrec || c == ``Eq.casesOn || c == ``Eq.subst ||
  c == ``HEq.rec || c == ``HEq.ndrec || c == ``Eq.mpr || c == ``Eq.mp


/-- Ledger 34: extensionality introductions whose lambda binders inherit
pair-aligned surface status (budget-capped), symmetric to the
destructuring-products rule — `funext`'s pointwise variable is the honest way
a proof reaches inside an extensional goal. -/
def extIntroHead (c : Name) : Bool :=
  c == ``funext || c == ``propext || c == ``Subtype.ext ||
  -- Mathlib names (not importable here; matched against the fixture env)
  c == `Set.ext || c == `SetLike.ext || c == `Finset.ext

/-- Refinement clause B : the head is a projection function
(structure or class field accessor — `And.right`, `Iff.mp`, `Fact.out`) whose
record argument is ante-involved: the application consumes an ante-derived fact,
so the arguments after the major feed the ante pipeline. -/
def projConsumerAnte (ctx : Ctx) (c : Name) (args : Array Expr)
    : MetaM (Option Nat) := do
  let some pi := ctx.env.getProjectionFnInfo? c | return none
  if pi.numParams < args.size then
    let major := args[pi.numParams]!
    if (← isProofSafe major) && (← anteInvolved ctx major) then
      return some pi.numParams
  return none

/-- Number of syntactic (no-unfold) forall binders. -/
def syntacticArity : Expr → Nat
  | .forallE _ _ b _ => syntacticArity b + 1
  | _ => 0

/-- Slot kinds of the ante's syntactic telescope: `true` = data (non-Prop). -/
def anteSlotKinds (ty : Expr) : MetaM (Array Bool) :=
  forallTelescope ty fun xs _ => xs.mapM fun x => do
    let t ← inferType x
    pure !(← try Meta.isProp t catch _ => pure true)

/-- Pair-aligned surface DATA depth of the goal : data binders of
the goal's syntactic telescope, extended by whnf-unfolding its conclusion
while the ante's data surface is deeper — the boundary is set by the depth
at which the PAIR speaks, not by either statement's presentation alone.
Prop binders neither count nor consume: by proof irrelevance they cannot
change which statement an ante instance asserts. -/
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
    else return n

/-- Ledger 34 conviction core: first DATA fvar in `a`'s closure lying outside
the established surface. Prop fvars are exempt everywhere — by proof
irrelevance they cannot change which statement an ante instance asserts. -/
def surfaceViolation? (ctx : Ctx) (a : Expr) : MetaM (Option FVarId) := do
  let surface ← ctx.surfaceFVars.get
  for fv in (Lean.collectFVars {} a).fvarIds do
    unless surface.contains fv do
      if let some d ← fv.findDecl? then
        let isPf ← try Meta.isProp d.type catch _ => pure true
        if !isPf then return some fv
  return none

/-- Ledger 37: resolve a let/have-bound fvar to its recorded value
(transitively), so the carrier rules judge the construction, not the name. -/
partial def resolveLocal (ctx : Ctx) (e : Expr) : MetaM Expr := do
  if e.isFVar then
    if let some v := (← ctx.localValues.get).get? e.fvarId! then
      return ← resolveLocal ctx v
  return e

/-- Ledger 37(B): does the goal's own (opened) statement mention `e`? The
audits' standard is "the ante must be used at the objects the pair's
statements speak about" — the goal's statement type is the ground truth of
what it speaks about. -/
def occursInGoalStmt (ctx : Ctx) (e : Expr) : MetaM Bool := do
  let parts := (← ctx.goalOpenParts.get).push (← ctx.goalTypeRem.get)
  return parts.any fun p => (p.find? (· == e)).isSome

/-- Severe tier of the ante-argument warning . Traverse `e`, looking
through have/let-bound locals, and report (draws on a local PROPOSITION,
mentions a local VARIABLE at all). A local proposition is a valueless
Prop-typed fvar (a hypothesis), an ante-involved fvar, the antecedent itself,
or an env-local constant that reaches the antecedent. -/
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
        if ← (try Meta.isProp ty catch _ => pure false) then prop.set true
  | .const c _ => do
    if c == ctx.ante then prop.set true
    else if isLocal ctx.env c then
      if ← constReaches ctx ctx.reachMemo ctx.ante c then prop.set true
  | .app f a => do localityGo ctx seen prop data f; localityGo ctx seen prop data a
  | .lam _ t b _ => do localityGo ctx seen prop data t; localityGo ctx seen prop data b
  | .forallE _ t b _ => do localityGo ctx seen prop data t; localityGo ctx seen prop data b
  | .letE _ t v b _ => do
    localityGo ctx seen prop data t; localityGo ctx seen prop data v; localityGo ctx seen prop data b
  | .mdata _ b => localityGo ctx seen prop data b
  | .proj _ _ b => localityGo ctx seen prop data b
  | _ => pure ()

def localityOf (ctx : Ctx) (e : Expr) : MetaM (Bool × Bool) := do
  let seen ← IO.mkRef ({} : FVarIdSet)
  let prop ← IO.mkRef false
  let data ← IO.mkRef false
  localityGo ctx seen prop data e
  return (← prop.get, ← data.get)

/-- If judging the head `c` just raised an ante-argument content warning, add
the severe tier when the whole application draws on no local proposition. -/
def severeIfClosed (ctx : Ctx) (nBefore : Nat) (c : Name) (args : Array Expr) : MetaM Unit := do
  let flags ← ctx.flags.get
  let fresh := flags.extract nBefore flags.size
  unless fresh.any (fun s => (s.splitOn "feeding ante application").length > 1) do return ()
  let (prop, data) ← localityOf ctx (mkAppN (.const c []) args)
  unless prop do
    let note := if data then "" else ", nor on any local variable"
    ctx.flag s!"severe: outside fact {c} feeding ante application draws on no local hypothesis{note}"

mutual

partial def walkLam (ctx : Ctx) (role : Role) (neg : Nat) (bindersAnte : Bool)
    : Expr → MetaM Unit
  | .lam n t b bi => do
    withLocalDecl n bi t fun x => do
      if bindersAnte then ctx.anteFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body)
      walkLam ctx role neg' bindersAnte body
  | e => walk ctx role neg e

/-- Like `walkLam`, additionally collecting the lambda-chain's binder ids —
refinement clause A needs the destructuring products' identities. -/
partial def walkLamCollect (ctx : Ctx) (role : Role) (neg : Nat)
    (bindersAnte : Bool) (markSurface : Bool) (acc : IO.Ref (Array FVarId))
    : Expr → MetaM Unit
  | .lam n t b bi => do
    withLocalDecl n bi t fun x => do
      acc.modify (·.push x.fvarId!)
      if bindersAnte then ctx.anteFVars.modify (·.insert x.fvarId!)
      -- products of a surface-rooted destructuring are the goal's
      -- own objects (a witness extracted from a surface hypothesis is surface)
      if markSurface then ctx.surfaceFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body)
      walkLamCollect ctx role neg' bindersAnte markSurface acc body
  | e =>
    -- surface-rooted destructuring: the continuation stays on the surface
    -- chain, so conclusion binders intro'd after an `obtain` still reach
    -- the alignment budget
    if markSurface then walkLamSurface ctx role neg e
    else walk ctx role neg e

/-- Ledger 34: peel a lambda chain, marking binders as pair-aligned surface
while the alignment budget (`surfaceLeft`) lasts. Entry point for the goal
proof's leading lambdas AND for extensionality introductions (a `funext`
binder is the goal speaking at the pair-aligned depth — the propositional
fold that `whnf` extension cannot open). -/
partial def walkLamSurface (ctx : Ctx) (role : Role) (neg : Nat) : Expr → MetaM Unit
  | .mdata _ b => walkLamSurface ctx role neg b
  | .lam n t b bi => do
    withLocalDecl n bi t fun x => do
      -- open the goal's statement with the walk's own fvars
      let rem ← ctx.goalTypeRem.get
      if let .forallE _ d body _ := rem then
        ctx.goalOpenParts.modify (·.push d)
        ctx.goalTypeRem.set (body.instantiate1 x)
      -- data binders consume the alignment budget; Prop binders are exempt
      -- from the conviction, so they neither consume nor need marking
      let isPf ← try Meta.isProp t catch _ => pure false
      if !isPf then
        if (← ctx.surfaceLeft.get) > 0 then
          ctx.surfaceLeft.modify (· - 1)
          ctx.surfaceFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body)
      walkLamSurface ctx role neg' body
  | .letE n t v b _ =>
    -- surface passthrough: the goal's own binders may be intro'd AFTER
    -- have/let steps; the peeler continues through bindings so the budget
    -- reaches them (putnam_1999_a6 / 2008_b4 class)
    handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default⟩ true
  | e => do
    if let some bind := asBinding? e then handleBinding ctx role neg bind true
    else walk ctx role neg e

partial def walk (ctx : Ctx) (role : Role) (neg : Nat) (e : Expr) : MetaM Unit := do
  match e with
  | .bvar _ | .mvar _ | .sort _ | .lit _ => pure ()
  | .fvar id =>
    recordOcc ctx id role
    checkFalseNode ctx neg e "hypothesis of type False"
  | .const c _ => do
    let nFlagsBefore := (← ctx.flags.get).size
    if c == ctx.ante then pure ()
    else if ctx.assumed.contains c then judgeOutsideLocal ctx role c
    else if isLocal ctx.env c then
      if c.isInternalDetail || (← constReaches ctx ctx.reachMemo ctx.ante c) then
        expandLocal ctx role neg c
      else judgeOutsideLocal ctx role c
    else judgeConst ctx role neg c "bare constant"
    if role == .anteArg then severeIfClosed ctx nFlagsBefore c #[]
  | .mdata _ b => walk ctx role neg b
  | .proj _ _ b =>
    checkFalseNode ctx neg e "projection"
    walk ctx role neg b
  | .lam .. => walkLam ctx role neg false e
  | .forallE .. => pure ()   -- a Pi in proof position is a type; nothing to judge
  | .letE n t v b _ =>
    handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default⟩
  | .app .. =>
    if let some bind := asBinding? e then
      handleBinding ctx role neg bind
    else do
      checkFalseNode ctx neg e "application"
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const c _ =>
        -- an exFalso head fed by a benign noConfusion `False`
        -- is impossible-branch elimination. The guard (bare-variable
        -- equation + whnf-reduction to `False`) certifies the branch is
        -- computationally dead, so its arguments walk at SIDE — nothing
        -- under a dead literal branch can do goal work, and a DERIVED
        -- equation fails the guard and keeps the eliminator convicted.
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
        -- head judging, by family (#3/#4)
        let isAss := ctx.assumed.contains c
        let isLoc := !isAss && c != ctx.ante && isLocal ctx.env c
        let locInternal := isLoc && c.isInternalDetail
        let locInvolved ← if isLoc && !locInternal then
            constReaches ctx ctx.reachMemo ctx.ante c
          else pure false
        let isLocFree := isLoc && !locInternal && !locInvolved
        let nFlagsBefore := (← ctx.flags.get).size
        if c == ctx.ante then pure ()
        else if isAss || isLocFree then judgeOutsideLocal ctx role c
        else if isLoc then expandLocal ctx role neg c
        else judgeConst ctx role neg c "application head"
        if role == .anteArg then severeIfClosed ctx nFlagsBefore c args
        -- argument dispatch
        if c == ctx.ante || locInvolved then
          -- carrier-affinity audit : a Sort-valued instantiation
          -- of the ante that is foreign to the goal's carriers convicts iff
          -- it occurs in what the ante DELIVERS here (a dead junk parameter
          -- is harmless) and the goal does not itself existentially bind a
          -- Sort (a type witness is arbitrary by nature)
          if c == ctx.ante then
            let delivered? ← inferTypeSafe e
            if !ctx.goalSortExists then
              for a in args do
                if let some ty ← inferTypeSafe a then
                  if ty.isSort && foreignCarrier ctx a then
                    if let some rty := delivered? then
                      if (rty.find? (· == a)).isSome then
                        ctx.fail s!"ante instantiated at a carrier foreign to the goal statement ({← Meta.ppExpr a})"
            -- data-surface instantiation audit : the ante's surface
            -- DATA slots must be filled at the goal's own surface objects — an
            -- argument capturing an off-surface data fvar uses the ante as a
            -- schema at objects the pair never speaks about. Load-bearing
            -- (delivery-occurrence) mirrors ; Prop fvars exempt.
            let slotData ← ctx.anteSlotData.get
            for i in [0:min args.size slotData.size] do
              if slotData[i]! then
                let a := args[i]!
                if a.hasFVar then
                  -- INSTANCE-SLOT STRICTNESS. The carrier doctrine one
                  -- level up — the ante must be applied at the goal's own STRUCTURES,
                  -- not just its objects. A class-typed argument in a data slot is
                  -- an instance slot; if its class sits on a goal-surface carrier and
                  -- the argument is not the goal's own instance binder, two shapes
                  -- convict:
                  --   (base) NON-subsingleton class the goal itself binds, filled
                  --     with a replaced structure not defeq to the goal's instance
                  --     (Pugh 2.92 / 1081: TopologicalSpace filled with ⊤). The
                  --     substitution changes meaning because the class is not a
                  --     subsingleton.
                  --   (ii)  SUBSINGLETON but content-bearing (Fintype) manufactured
                  --     when the goal statement grants no such structure (0459:
                  --     Fintype minted from vacuous hypotheses). Subsingleton alone
                  --     does not exempt — the interchange argument presupposes the
                  --     goal HAS an instance to interchange with.
                  -- Exemptions: defeq to the goal's own instance; the instance occurs
                  -- in the goal's statement; classically-free scaffolding
                  -- (Decidable/DecidableEq, synthesizable with a universal classical
                  -- Decidable-provider — no class-name whitelist); or, for content
                  -- subsingletons, the goal statement itself grants the structure
                  -- (Finite/Fintype binder — the honest Finite→Fintype upgrade).
                  if let some clsType ← inferTypeSafe a then
                    if let some clsName ← (try Meta.isClass? clsType catch _ => pure none) then
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
                              if (← try Meta.isDefEq d.type clsType catch _ => pure false) then
                                goalInst := some fv
                        let defeqGoal ← match goalInst with
                          | some g => try Meta.isDefEq a (mkFVar g) catch _ => pure false
                          | none => pure false
                        let subsing ← do
                          match ← (try Meta.synthInstance? (← Meta.mkAppM ``Subsingleton #[clsType]) catch _ => pure none) with
                          | some _ => pure true
                          | none => pure false
                        -- classically-free scaffolding test (Decidable/DecidableEq):
                        -- synthesizable given a universal classical Decidable-provider?
                        let synthCl ← do
                          try
                            let decProv := Expr.forallE `p (mkSort Level.zero)
                              (mkApp (mkConst ``Decidable) (Expr.bvar 0)) BinderInfo.default
                            Meta.withLocalDecl `cd BinderInfo.instImplicit decProv fun cd =>
                              Meta.withNewLocalInstance ``Decidable cd do
                                pure (← Meta.synthInstance? clsType).isSome
                          catch _ => pure false
                        -- does the goal STATEMENT grant finiteness (Finite/Fintype)?
                        let goalFin := ctx.goalHasFin
                        let occGoal := (← occursInGoalStmt ctx a) || (← occursInGoalStmt ctx argCore)
                        unless defeqGoal || occGoal do
                          if !subsing then
                            -- base: replaced non-subsingleton structure the goal binds
                            if goalInst.isSome then
                              ctx.fail s!"ante instance slot at a surface carrier filled with a replaced {clsName} structure ({← Meta.ppExpr a}); the goal's own instance is unused"
                          else
                            -- (ii): content subsingleton manufactured, goal grants none;
                            -- classically-free scaffolding stays exempt
                            if !synthCl && !goalFin then
                              ctx.fail s!"ante instance slot at a surface carrier filled with a manufactured {clsName} instance ({← Meta.ppExpr a}) the goal statement does not grant"
                  let isSortSlot ← do
                    match ← inferTypeSafe a with
                    | some ty => pure ty.isSort
                    | none => pure false
                  if isSortSlot && !ctx.goalSortExists then
                    -- (Pugh 2.92 ruling): a Sort-valued surface slot
                    -- must be the goal's OWN carrier — a type constructed from
                    -- goal data (`↥(s 0)`) is related but not the same carrier;
                    -- transports remain legal for VALUE slots only
                    -- PLift/ULift transparency : universe
                    -- adapters are content-free; test the wrapped core.
                    -- Ledger 37: resolve let-bound names to their values first.
                    let mut core ← resolveLocal ctx a
                    while core.isAppOfArity ``PLift 1 || core.isAppOfArity ``ULift 1 do
                      core ← resolveLocal ctx (core.getArg! 0)
                    let bareSurface := core.isFVar &&
                      (← ctx.surfaceFVars.get).contains core.fvarId!
                    if !bareSurface then
                      -- a type the goal's own statement mentions
                      -- IS the goal's own object (0648 cand→ref: `↥F` occurs
                      -- inside `IsAlgebraic F a`)
                      if !(← occursInGoalStmt ctx a) && !(← occursInGoalStmt ctx core) then
                        if let some rty := delivered? then
                          if (rty.find? (· == a)).isSome then
                            ctx.fail s!"ante carrier slot instantiated at a type constructed from, not identical to, the goal's carriers ({← Meta.ppExpr a})"
                  else
                    -- : a VALUE slot whose
                    -- argument the delivered conclusion uses AS A TYPE (the
                    -- coercion ↥arg appears) is carrier-inducing — the
                    -- carrier of the delivered statement must be the goal's
                    -- own object (l.36 strictness), while plain value use
                    -- keeps the lenient transport rule below
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
                      if !(← occursInGoalStmt ctx a) && !(← occursInGoalStmt ctx vcore) then
                        ctx.fail s!"ante value slot used as a carrier of the delivered statement but instantiated at a constructed object ({← Meta.ppExpr a})"
                    else
                      if let some fv ← surfaceViolation? ctx a then
                        if let some rty := delivered? then
                          if (rty.find? (· == a)).isSome then
                            ctx.fail s!"ante surface slot instantiated at an object outside the statements' shared surface ({← Meta.ppExpr a}; foreign object {← Meta.ppExpr (mkFVar fv)})"
          -- the ante, or an ante-involved local lemma: its arguments feed the
          -- ante pipeline
          for a in args do walk ctx .anteArg neg a
        else if transitionHead c then
          -- the role-transition rule : a transition transports
          -- the ROLE with the content — the converted proof (last arg) inherits
          -- the conversion's position; the RECORD (the equation/iff being used,
          -- second-to-last arg) is ancillary AS A WHOLE and walks at SIDE.
          ctx.chainCtx.modify (·+1)
          for i in [0:args.size] do
            let r := if args.size ≥ 2 && i == args.size - 2 then Role.side else role
            walk ctx r neg args[i]!
          ctx.chainCtx.modify (·-1)
        else if recordHead c then
          ctx.chainCtx.modify (·+1)
          for i in [0:args.size] do
            let r := if i == args.size - 1 then Role.side else role
            walk ctx r neg args[i]!
          ctx.chainCtx.modify (·-1)
        else if let some majorIdx ← projConsumerAnte ctx c args then
          -- refinement clause B: `And.right hod' u …` — args after the
          -- ante-involved record argument feed an ante-derived fact
          for i in [0:args.size] do
            walk ctx (if i > majorIdx then .anteArg else role) neg args[i]!
        else if ← isEliminatorConst ctx.env c then
          -- eliminator arm BEFORE the bridge arm
          -- an Eq.rec-family substitution is a transport position
          -- (census bump only; routing unchanged)
          if eqRecFamily c then ctx.chainCtx.modify (·+1)
          let mut majorInv := false
          let mut majorSurface := true
          for a in args do
            if !a.isLambda then
              if (← isProofSafe a) && (← anteInvolved ctx a) then majorInv := true
              if a.hasFVar then
                if (← surfaceViolation? ctx a).isSome then majorSurface := false
          -- refinement clause A: walk minors FIRST, collecting product binders;
          -- a destructured local's occurrence then takes its products' role join
          let products ← IO.mkRef (#[] : Array FVarId)
          let mut minors := #[]
          for a in args do
            if a.isLambda then
              if ← isProofSafe a then
                -- a genuine minor: its binders are the destructuring products
                walkLamCollect ctx role neg majorInv majorSurface products a
                minors := minors.push a
                if role == .goal && !majorInv then
                  branchAblation ctx a s!"branch of {c}"
              else
                -- motive / predicate lambda: type-level, no products to collect
                walkLam ctx role neg majorInv a
          -- (dead-elimination audit, backup): the
          -- ablation exemption for ante-involved eliminations must be EARNED —
          -- when the destructuring produced binders and EVERY one is unused,
          -- it distributed nothing (a dead occurrence of the ante) and the
          -- default rule resumes on its branches. Binder-less case splits and
          -- partially-used destructurings are untouched.
          if role == .goal && majorInv && minors.size > 0 then
            let prods ← products.get
            if prods.size > 0 then
              let occ ← ctx.occRoles.get
              if prods.all (fun p => (occ.get? p).isNone) then
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
        else if extIntroHead c then
          for a in args do
            if a.isLambda then
              if ← isProofSafe a then
                -- the pointwise proof: its binders inherit surface (budgeted)
                walkLamSurface ctx role neg a
                if role == .goal then branchAblation ctx a "lambda argument"
              else
                -- motive / type-family lambda: no surface budget
                walkLam ctx role neg false a
            else walk ctx role neg a
        else if ← headIsBridge ctx c (isAss || isLocFree) then
          -- rule (a) RESCOPED : a bridge applied FORWARD is
          -- role-transparent — its hypotheses are constitutive inputs
          -- (`le_antisymm h1 h2`: the h's ARE the content), not side conditions.
          -- Ancillary protection now lives at the RECORD sites (transitions /
          -- rewrite machinery), where whole equation-manufacture walks at SIDE.
          -- (the bare-bridge rule,): a plain-Eq/Iff
          -- library lemma is licensed to TRANSPORT content between phrasings;
          -- asserted at GOAL role outside every transport position
          -- (transition/record/Eq.rec-substitution/cast/equational-chain leg)
          -- with an ante-free cone, its conclusion stands as mathematical
          -- content — the Artin 2.8.6 `Set.center_prod` class
          if role == .goal && (← ctx.chainCtx.get) == 0 && !isLoc && !isAss then
            if ← plainEqIffConcl ctx.env c then
              if !(← anteInvolved ctx e) then
                ctx.fail s!"bridge conclusion asserted as content at goal role (bare, ante-free, outside transport position): {c}"
          let chain := c == ``Eq.trans || c == ``Eq.symm || c == ``Iff.trans ||
            c == ``Iff.symm || c == ``congrArg || c == ``congrFun ||
            c == ``congr || c == ``Trans.trans || c == ``HEq.trans || c == ``HEq.symm
          for a in args do
            if chain then
              ctx.chainCtx.modify (·+1)
              walk ctx role neg a
              ctx.chainCtx.modify (·-1)
            else walk ctx role neg a
        else
          let dataHead ← if isAss || isLoc then pure false
            else pure ((← categorize ctx c) == .data)
          if c == ``cast then ctx.chainCtx.modify (·+1)
          for a in args do
            walk ctx role neg a
            if role == .goal && a.isLambda && !dataHead then
              branchAblation ctx a "lambda argument"
          if c == ``cast then ctx.chainCtx.modify (·-1)
      | .fvar id =>
        recordOcc ctx id role
        let anteHead := (← ctx.anteFVars.get).contains id
        for a in args do
          walk ctx (if anteHead then .anteArg else role) neg a
      | .proj sName _ s =>
        -- Iff/Eq projections are TRANSITIONS: record at SIDE, converted proof
        -- inherits the role; other projections keep clause B
        checkFalseNode ctx neg f "projection"
        if sName == ``Iff || sName == ``Eq then
          walk ctx .side neg s
          for a in args do walk ctx role neg a
        else
          walk ctx role neg s
          let inv ← anteInvolved ctx s
          for a in args do walk ctx (if inv then .anteArg else role) neg a
      | _ =>
        walk ctx role neg f
        for a in args do walk ctx role neg a

/-- Bridge-arm test for an application head: globals via `categorize`, assumed /
ante-free local lemmas via their graded statement (#3/#4). -/
partial def headIsBridge (ctx : Ctx) (c : Name) (outsideLocal : Bool) : MetaM Bool := do
  if outsideLocal then
    return ((← ctx.localGrade.get).find? c).getD false
  else
    return (← categorize ctx c) == .bridge

/-- Ablation check: at role GOAL, a proof whose dependency cone AND whose type's
cone are both ante-free closes a goal part without the antecedent. -/
partial def branchAblation (ctx : Ctx) (a : Expr) (locus : String) : MetaM Unit := do
  unless ← isProofSafe a do return ()
  if ← anteInvolved ctx a then return ()
  let some ty ← inferTypeSafe a | return ()
  if ← anteInvolved ctx ty then return ()
  ctx.fail s!"goal part closes ante-free ({locus})"

partial def handleBinding (ctx : Ctx) (role : Role) (neg : Nat) (b : Binding)
    (surfaceMode : Bool := false) : MetaM Unit := do
  let vInv ← anteInvolved ctx b.value
  let propT ← try Meta.isProp b.binderType catch _ => pure false
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
    let neg' := neg + (← negBump body)
    if surfaceMode then walkLamSurface ctx role neg' body
    else walk ctx role neg' body
    -- ablation locus (i): the rest of the proof after this binding
    if role == .goal then
      if !(← anteInvolved ctx body) then
        if ← isProofSafe body then
          let tyOk ← do
            match ← inferTypeSafe body with
            | some ty => pure !(← anteInvolved ctx ty)
            | none => pure false
          if tyOk then
            ctx.fail s!"goal part closes ante-free (body after binding {b.binderName})"
    let jr := ((← ctx.occRoles.get).get? x.fvarId!)
    if vInv then
      if ← auditTrace then IO.eprintln s!"[trace] ante-involved binding {b.binderName} walked @ {((jr.getD role)).str}"
      walk ctx (jr.getD role) neg b.value
    else if propT then
      -- RULE 2: ante-free Prop local = outside lemma; sorry scan on the value.
      if ← auditTrace then do
        let jrs := (jr.map Role.str).getD "unused"
        IO.eprintln s!"[trace] RULE2 have {b.binderName} jr={jrs}"
      if ← reachesSorry ctx b.value then ctx.sorryHit.set true
      if ← bridgeGradeType ctx.env b.binderType then
        -- local bridge admitted — flag if it quotes the goal
        if ← goalShaped ctx b.binderType then
          ctx.flag s!"goal-shaped local bridge (have {b.binderName})"
      else
        match jr with
        | some .goal =>
          ctx.fail s!"bare-Prop local hypothesis {b.binderName} used on goal spine"
        | some .anteArg =>
          ctx.flag s!"bare-Prop local hypothesis {b.binderName} feeding ante application"
          let (prop, data) ← localityOf ctx b.value
          unless prop do
            let note := if data then "" else ", nor on any local variable"
            ctx.flag s!"severe: bare-Prop local hypothesis {b.binderName} feeding ante application is proved without any local hypothesis{note}"
        | some .side | none => pure ()
    else
      walk ctx (jr.getD role) neg b.value

end

/-- Split a goal conclusion into its ∧-parts (goal-part support). -/
partial def splitAnd (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``And 2 then
    splitAnd (e.getArg! 1) (splitAnd (e.getArg! 0) acc)
  else acc.push e

def computeGoalParts (goalType : Expr) : MetaM (Array Expr) := do
  try
    let (_, _, concl) ← forallMetaTelescope goalType
    return splitAnd concl
  catch _ => return #[]

/-- Differential reproof outcome : the armed probe's
success has two causes the single probe conflated — the confiscated
constructions enabled the ante-free close (middleman → convict), or the goal
was provable bare (library-true → a pair property, flagged not convicted). -/
inductive ReproofOutcome | silent | middleman | libraryTrue
deriving BEq

/-- Confiscated-instances reproof : on an otherwise-PASSing
direction, rebuild the goal's telescope, re-assert every ANTE-FREE local binding
the proof itself constructed (data bindings as INSTANCES — the confiscation:
the adversary's packaging is turned against it), and ask a weak prover to close
the conclusion without the ante. Ante-involved bindings are never confiscated
(witness extraction must not leak ante content into the "ante-free" probe);
collection stops at the first one.

Differential form : armed success alone no
longer convicts; a BARE probe (no confiscation) then classifies it. Bare
failure means the proof's own packaging was load-bearing for the ante-free
close — middleman, convict. Bare success means the conclusion is
library-provable outright — no implication proof can witness or launder
anything there; flagged `library-true`, not convicted. -/
partial def confiscatedReproof (ctx : Ctx) (goalName : Name)
    (goalType proofVal : Expr) : Term.TermElabM ReproofOutcome := do
  try
    forallTelescope goalType fun xs concl => do
      let mut body := proofVal
      for x in xs do
        match body with
        | .lam _ _ b _ => body := b.instantiate1 x
        | .mdata _ (.lam _ _ b _) => body := b.instantiate1 x
        | _ => break
      if !(← collect concl body) then return .silent
      if ← probe concl then return .libraryTrue
      return .middleman
  catch _ => return .silent
where
  /-- The probe searches the fixture's own env, which contains the proven goal
  theorem and the sorried ante/assumed — a probe proof reaching any of them is
  circular, not evidence of ante-free provability. -/
  legalProof (proof : Expr) : Term.TermElabM Bool := do
    let forbidden : NameSet := (ctx.assumed.insert ctx.ante).insert goalName
    let mut queue := proof.getUsedConstantsAsSet.toList
    let mut visited : NameSet := {}
    while h : !queue.isEmpty do
      let c := queue.head (by simpa using h)
      queue := queue.tail
      if visited.contains c then continue
      visited := visited.insert c
      if forbidden.contains c then return false
      if isLocal ctx.env c then
        if let some v := valueOf? ctx.env c then
          queue := v.getUsedConstantsAsSet.toList ++ queue
    return true
  probe (concl : Expr) : Term.TermElabM Bool := do
    for script in #["assumption", "exact?"] do
      if let some proof ← tryScript concl script then
        if ← legalProof proof then
          return true
    return false
  collect (concl : Expr) : Expr → Term.TermElabM Bool
    | e => do
      match asBinding? e with
      | some b => do
        let tInv ← anteInvolved ctx b.binderType
        let vInv ← anteInvolved ctx b.value
        if tInv || vInv then
          probe concl   -- stop confiscating at the first ante-involved binding
        else
          -- confiscate BY VALUE (withLetDecl): an opaque hypothesis of the same
          -- class is useless — the goal's operations are pinned to the goal's own
          -- instances, and only the actual constructed value (which extends them)
          -- is defeq-linked to the goal
          Meta.withLetDecl b.binderName b.binderType b.value fun x => do
            match ← try Meta.isClass? b.binderType catch _ => pure none with
            | some cls => Meta.withNewLocalInstance cls x <| collect concl (b.mkBody x)
            | none => collect concl (b.mkBody x)
      | none => do
        -- `letI` is often zeta-inlined: the constructed instance sits INLINE as
        -- an argument of the terminal application (`assumed … (toCommRing {…}) …`).
        -- Confiscate every ante-free, non-fvar, class-typed argument.
        inline concl e.getAppArgs 0
  inline (concl : Expr) (args : Array Expr) (i : Nat) : Term.TermElabM Bool := do
    if h : i < args.size then
      let a := args[i]
      let take ← do
        if a.isFVar then pure none
        else if ← anteInvolved ctx a then pure none
        else match ← inferTypeSafe a with
          | some ty =>
            match ← try Meta.isClass? ty catch _ => pure none with
            | some cls => pure (some (cls, ty))
            | none => pure none
          | none => pure none
      match take with
      | some (cls, ty) =>
        Meta.withLetDecl `inst ty a fun x =>
          Meta.withNewLocalInstance cls x <| inline concl args (i+1)
      | none => inline concl args (i+1)
    else
      probe concl

structure FixtureResult where
  file    : String
  verdict : String
  flags   : Array String := #[]
  reasons : Array String := #[]
  ante    : Name := .anonymous
  goal    : Name := .anonymous
  assumed : Array Name := #[]

def FixtureResult.toJson (r : FixtureResult) : Json :=
  Json.mkObj
    [ ("file", Json.str r.file)
    , ("verdict", Json.str r.verdict)
    , ("flags", Lean.ToJson.toJson r.flags.size)
    , ("flagDetails", Json.arr (r.flags.map Json.str))
    , ("reasons", Json.arr (r.reasons.map Json.str))
    , ("ante", Json.str r.ante.toString)
    , ("goal", Json.str r.goal.toString)
    , ("assumed", Json.arr (r.assumed.map (Json.str ·.toString))) ]

/-- Human-readable rendering of a fixture verdict (the default stdout format;
`--raw` prints the JSON record instead): the verdict first, then the reasons
of a rejection, or only the severe warnings of an acceptance. -/
def FixtureResult.render (r : FixtureResult) : String := Id.run do
  let mut out := s!"── {r.file}\n   verdict: {r.verdict}"
  if r.ante != .anonymous then out := out ++ s!"   (antecedent {r.ante}, goal {r.goal})"
  out := out ++ "\n"
  if r.verdict == "PASS" then
    let severe := r.flags.filter (·.startsWith "severe:")
    if severe.isEmpty then out := out ++ "   severe warnings: none\n"
    else
      out := out ++ "   severe warnings:\n"
      for f in severe do out := out ++ s!"      {f}\n"
  else
    if r.reasons.isEmpty then out := out ++ "   reasons: none recorded\n"
    else
      out := out ++ "   reasons:\n"
      for x in r.reasons do out := out ++ s!"      {x}\n"
  return out

/-- Theorem names in source order (top-level `theorem`/`lemma` declarations). -/
def declaredThmNames (src : String) : Array Name := Id.run do
  let mut out := #[]
  for line in src.splitOn "\n" do
    let l := line.trimAsciiStart.copy
    for kw in ["theorem ", "lemma "] do
      if l.startsWith kw then
        let rest := (l.drop kw.length).trimAsciiStart.copy
        let ident := String.ofList <| rest.toList.takeWhile fun ch =>
          ch.isAlphanum || ch == '_' || ch == '\'' || ch == '.' || ch == '!' || ch == '?'
        if !ident.isEmpty then
          out := out.push ident.toName
  return out

/-- Audit one fixture file. -/
def auditFixture (path : String) : IO FixtureResult := do
  let src ← IO.FS.readFile path
  -- values of in-file theorems must be synchronously available for the term walk
  let compiled ← compileSide src path (opts := ({} : Options).setBool `Elab.async false)
  let some cmdState := compiled.cmdState?
    | return { file := path, verdict := "ERROR", reasons := compiled.report.errors }
  unless compiled.report.ok do
    return { file := path, verdict := "ERROR", reasons := compiled.report.errors }
  let env := cmdState.env
  let names := (declaredThmNames src).filter fun n => (env.find? n).isSome
  if names.size < 2 then
    return { file := path, verdict := "ERROR",
             reasons := #[s!"expected ≥2 theorems, found {names.size}"] }
  let reachesSorryRaw (c : Name) : Bool :=
    match valueOf? env c with
    | some v => v.getUsedConstantsAsSet.contains ``sorryAx
    | none => true
  -- goal = LAST non-sorried theorem; ante = last sorried theorem
  -- declared before it (fixture convention: preamble assumptions, then the
  -- assumed statement, then the goal); other sorried theorems = assumed set.
  let sorried := names.filter reachesSorryRaw
  let nonSorried := names.filter (fun n => !reachesSorryRaw n)
  let goal := nonSorried.back?.getD names.back!
  let goalIdx := (names.findIdx? (· == goal)).getD names.size
  let anteCands := sorried.filter fun n =>
    ((names.findIdx? (· == n)).getD names.size) < goalIdx
  let ante := anteCands.back?.getD (sorried.back?.getD names[0]!)
  let assumedArr := sorried.filter (· != ante)
  let assumed : NameSet := assumedArr.foldl (init := {}) (·.insert ·)
  let some goalVal := valueOf? env goal
    | return { file := path, verdict := "ERROR",
               reasons := #[s!"no value for goal theorem {goal}"], ante, goal }
  let goalType := ((env.find? goal).map (·.type)).getD (mkConst ``True)
  let goalConsts : NameSet :=
    goalType.getUsedConstantsAsSet.foldl (init := ({} : NameSet)) (·.insert ·)
  let goalPropCarrier :=
    (goalType.find? (fun e => e matches .sort .zero)).isSome
  let goalSortExists :=
    (goalType.find? (fun e =>
      e.isAppOfArity ``Exists 2 && (e.getArg! 0).isSort)).isSome
  let goalHasFin :=
    (goalType.find? (fun e => match e with
      | .forallE _ d _ _ => d.isAppOf `Finite || d.isAppOf `Fintype
      | _ => false)).isSome
  let ctx : Ctx := {
    env, ante, assumed, goalConsts, goalPropCarrier, goalSortExists, goalHasFin
    catMemo := ← IO.mkRef {}, reachMemo := ← IO.mkRef {}, sorryMemo := ← IO.mkRef {}
    localGrade := ← IO.mkRef {}, goalParts := ← IO.mkRef #[]
    occRoles := ← IO.mkRef {}, anteFVars := ← IO.mkRef {}
    surfaceFVars := ← IO.mkRef {}, surfaceLeft := ← IO.mkRef 0
    anteSlotData := ← IO.mkRef #[], localValues := ← IO.mkRef {}
    propValues := ← IO.mkRef {}
    chainCtx := ← IO.mkRef 0
    goalOpenParts := ← IO.mkRef #[], goalTypeRem := ← IO.mkRef (mkConst ``True)
    fails := ← IO.mkRef #[], flags := ← IO.mkRef #[]
    sorryHit := ← IO.mkRef false, expanded := ← IO.mkRef {} }
  let opts : Options := (maxHeartbeats.set {} 4000000)
  try
    runMetaM env opts do
      ctx.goalParts.set (← computeGoalParts goalType)
      let anteType := ((env.find? ante).map (·.type)).getD (mkConst ``True)
      let anteData ← anteSlotKinds anteType
      ctx.anteSlotData.set anteData
      let dataTarget := anteData.foldl (fun n b => if b then n+1 else n) 0
      ctx.surfaceLeft.set (max (← extendedSurfaceDataArity goalType dataTarget) dataTarget)
      ctx.goalTypeRem.set goalType
      if ← reachesSorry ctx goalVal then
        ctx.sorryHit.set true    -- WIP fixture: the goal proof itself is sorried
      else do
        if !(← anteInvolved ctx goalVal) then
          ctx.fail "proof never touches the antecedent"
        walkLamSurface ctx .goal 0 goalVal
  catch e =>
    return { file := path, verdict := "ERROR",
             reasons := #[s!"audit crashed: {toString e}"], ante, goal,
             assumed := assumedArr }
  if ← ctx.sorryHit.get then
    return { file := path, verdict := "SKIP_SORRY", ante, goal, assumed := assumedArr }
  let mut fails ← ctx.fails.get
  let mut flags ← ctx.flags.get
  if fails.isEmpty then
    -- Prefer probing in the PRISTINE import env: the fixture env contains the
    -- proven goal and the sorried ante, and `exact?` happily returns those
    -- circular candidates first. Only possible when the goal's statement uses
    -- no fixture-local vocabulary.
    let goalTypeClean := goalType.getUsedConstantsAsSet.toList.all
      fun c => !isLocal env c
    let reproofEnv ← do
      if goalTypeClean then
        try
          let inputCtx := Parser.mkInputContext src path
          let (header, _, _) ← Parser.parseHeader inputCtx
          let (cleanEnv, _) ← cachedImportModules (headerToImports header)
            (({} : Options).setBool `Elab.async false)
          pure cleanEnv
        catch _ => pure env
      else pure env
    let outcome ← try
        runTermElabM reproofEnv opts (confiscatedReproof ctx goal goalType goalVal)
      catch _ => pure ReproofOutcome.silent
    if outcome == .middleman then
      fails := fails.push
        "goal provable without the antecedent given the proof's own ante-free \
         local constructions (confiscated-instances reproof)"
    else if outcome == .libraryTrue then
      flags := flags.push
        "library-true goal: conclusion provable ante-free from the ambient \
         library (no equivalence evidence; differential reproof)"
  if fails.isEmpty then
    return { file := path, verdict := "PASS", flags, ante, goal, assumed := assumedArr }
  else
    return { file := path, verdict := "FAIL", flags, reasons := fails, ante, goal,
             assumed := assumedArr }

/-- Expand CLI paths: a directory contributes its immediate `*.lean` files except
`ref.lean`/`cand.lean`. -/
def expandPaths (paths : List String) : IO (Array String) := do
  let mut out := #[]
  for p in paths do
    if ← System.FilePath.isDir p then
      let entries ← System.FilePath.readDir p
      let files := entries.filterMap fun ent =>
        let n := ent.fileName
        if n.endsWith ".lean" && n != "ref.lean" && n != "cand.lean" then
          some ent.path.toString
        else none
      out := out ++ files.qsort (· < ·)
    else
      out := out.push p
  return out

def runProofCli (paths : List String) (raw : Bool := false) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: semanteq [--raw] --proof <fixture.lean|dir> [...]"
    return 1
  let files ← expandPaths paths
  for f in files do
    IO.eprintln s!"[proof-audit] {f}"
    let r ← auditFixture f
    if raw then IO.println r.toJson.compress else IO.print r.render
    (← IO.getStdout).flush
  return 0

end ProofAudit
end SemantEq
