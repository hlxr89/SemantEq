import Lean
import SemantEq.Config
import SemantEq.Logic

/-!
# The checker's context and constant grading

Roles (goal / antecedent-argument / side), the per-fixture context `Ctx`, the
categorical grading of global constants (`categorize`, `judgeConst`) and of
in-file lemmas (`judgeOutsideLocal`), and the reachability tests through
env-local values.
-/

namespace SemantEq
namespace ProofAudit
open Lean Elab Meta

/-- The role lattice, most demanding first: goal, antecedent argument, side. -/
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

/-- The ex-falso eliminators the checker bans: those of `False` and those of
the other empty types. -/
def exFalso5 : NameSet := emptyTypeEliminators.foldl (·.insert ·) exFalsoConstants

/-- Heads of the `noConfusion` family (auto-generated discriminators and
`noConfusion_of_Nat`-style helpers). -/
def nameHasNoConfusion (c : Name) : Bool :=
  ((toString c).splitOn "noConfusion").length > 1

/-- Category of a constant: the antecedent (sanctioned), `sorryAx`, an
ex-falso eliminator, data, logically schematic, a bridge, or content. -/
inductive Cat
  | sanctioned | sorryC | exFalso | data | schematic | bridge | content
deriving BEq, Repr

/-- The per-fixture context of the walk: the environment, the antecedent and
assumed names, the memos, the role bookkeeping, the surface and carrier
state, the nesting depths, the recorded failures and warnings, and the
switches. -/
structure Ctx where
  env        : Environment
  ante       : Name
  /-- the other sorried in-file theorems: outside lemmas with a licensed
  sorry, never sanctioned, never expanded, never rescuing a part from
  ablation -/
  assumed    : NameSet := {}
  catMemo    : IO.Ref (NameMap Cat)
  reachMemo  : IO.Ref (NameMap Bool)      -- local constant → reaches the antecedent?
  sorryMemo  : IO.Ref (NameMap Bool)      -- local constant → reaches sorryAx?
  localGrade : IO.Ref (NameMap Bool)      -- assumed or antecedent-free local: bridge-graded?
  goalParts  : IO.Ref (Array Expr)        -- ∧-split goal conclusion
  /-- every constant of the goal statement's type, plus whether `Prop` itself
  appears as a binder-domain carrier there; an antecedent application
  instantiating a type parameter whose vocabulary is disjoint from this set
  is off-subject (the carrier-affinity audit) -/
  goalConsts : NameSet := {}
  goalPropCarrier : Bool := false
  /-- the goal's conclusion existentially quantifies a Sort; its type witness
  is arbitrary by nature, so foreign carriers are legitimate there -/
  goalSortExists : Bool := false
  /-- does the goal statement's telescope bind a finiteness instance
  (`Finite`/`Fintype`)? Distinguishes the honest `Finite` to `Fintype`
  upgrade from a manufactured instance. Computed from the goal type, so a
  `have`-minted `Finite` in the proof body cannot spoof it. -/
  goalHasFin : Bool := false
  occRoles   : IO.Ref (FVarIdMap Role)
  /-- occurrences inside a rewrite record or a local bridge's proof, kept
  apart from the plain ones: a binding used only there is judged in the
  record regime (its value walked under `recordCtx`, where content flags and
  a collapse convicts), not on the goal spine -/
  recordOccRoles : IO.Ref (FVarIdMap Role)
  anteFVars  : IO.Ref FVarIdSet
  /-- fvars established as the pair-aligned statement surface: goal-telescope
  binders up to the aligned depth, surface-valued data bindings, and the
  destructuring products of surface-rooted eliminations (the data-surface
  audit) -/
  surfaceFVars : IO.Ref FVarIdSet
  /-- countdown of goal-proof leading lambdas still to mark as surface -/
  surfaceLeft : IO.Ref Nat
  /-- kinds of the antecedent's syntactic telescope binders: true = data (non-Prop) -/
  anteSlotData : IO.Ref (Array Bool)
  /-- the goal's statement, opened progressively with the walk's own fvars
  (binder domains already peeled, plus the remainder), so a carrier argument
  can be tested for occurrence in what the goal itself says (`↥F` inside
  `IsAlgebraic F a`) -/
  goalOpenParts : IO.Ref (Array Expr)
  goalTypeRem : IO.Ref Expr
  /-- depth inside a transport position (transitions, records, equational-chain
  legs, `cast`, `Eq.rec`-family substitutions, `Iff`/`Eq` projections) -/
  chainCtx : IO.Ref Nat
  /-- depth of converted proofs under a conversion whose justification is
  antecedent-involved (`Eq.mpr`, `Eq.mp`, `Iff.mp`, `Iff.mpr`, `cast`, an
  `Eq.rec` substitution): the goal is frozen there, and a constructor's
  components are the residual obligation of the antecedent's rewrite, not
  goal parts -/
  frozenCtx : IO.Ref Nat
  /-- depth inside a rewrite or transition record, the equation or
  biconditional a conversion rewrites along. Records are walked at the
  enclosing role; a content constant met there is a flag, not a failure,
  since a conditional bridge's side condition may be met by any fact, while
  a goal part collapsed to `True` by a content fact inside a record is
  refused. -/
  recordCtx : IO.Ref Nat
  /-- depth inside the proof of an antecedent-free local bridge, read at the
  bridge's use role. Goal-part ablations are suspended there (the sub-proof
  proves the bridge, not the goal) and content is graded at the flag tier. -/
  localProofCtx : IO.Ref Nat
  /-- depth inside a direction of a local bridge's proof (a Prop-binder lambda
  met under `localProofCtx`): the direction is read as an implication proof of
  its own, its hypothesis in the antecedent's role (`directionAblation`) -/
  dirCtx : IO.Ref Nat
  /-- inline walks of an antecedent-involved in-file helper's body, per helper
  (capped, to bound repeated expansion) -/
  helperWalks : IO.Ref (NameMap Nat)
  /-- values of local data bindings: the carrier rules resolve a let-bound
  name to its value before the bare-surface test, or `let X :=
  <construction>` would slip past them -/
  localValues : IO.Ref (FVarIdMap Expr)
  /-- severe-warning tier: values of local Prop bindings (`have`), so a use of
  an outside fact can be tested for whether it draws on any local hypothesis
  through such a binding -/
  propValues : IO.Ref (FVarIdMap Expr)
  fails      : IO.Ref (Array String)
  flags      : IO.Ref (Array String)
  sorryHit   : IO.Ref Bool
  expanded   : IO.Ref NameSet             -- local constants already looked through
  /-- the reproof's extended collection looks through the proof's goal-side
  structure (case splits on goal hypotheses, intros, ante-free goal
  conversions) and re-asserts every ante-free local binding it meets before
  probing; `SEMANTEQ_NO_REPLAY_LOCAL_FACTS=1` restricts it to the leading
  have/let chain (ablation). -/
  replayLocalFacts : Bool := true
  /-- the closed-witness audit: audit the witnesses the proof supplies for the antecedent's
  existential hypotheses (`witnessAudit`); `SEMANTEQ_NO_WITNESS_CHECK=1`
  disables it (ablation). -/
  witnessCheck : Bool := true
  /-- the goal's closed statement (the witness audit's occurrence test) -/
  goalStmt : Expr := mkConst ``True
  /-- the conjunct-level ablation: ablate the components of `And.intro` / `Iff.intro` on the goal spine;
  `SEMANTEQ_NO_CONJUNCT_ABLATION=1` disables it (ablation). -/
  conjunctAblation : Bool := true
  /-- `--strict` / `SEMANTEQ_STRICT`: the strict reading. A severe use (a
  library fact, or a local hypothesis proved from nothing local, meeting a
  hypothesis of the antecedent while drawing on no local hypothesis) fails
  the proof instead of being recorded, at the top level and inside the
  proofs of local bridges alike. Off by default: the shape admission of
  local bridges and the tolerance are the standard rules, and strict adds
  to them. The reading of local bridge proofs itself runs in both modes
  (`directionAblation`). -/
  strictLocalProofs : Bool := false
  /-- a proof-typed lambda component of `And.intro`, `Iff.intro` or
  `Exists.intro` at goal role binds the goal statement's own objects (the ∀
  inside a conjunct), so its data binders draw on the surface budget like
  the goal's leading lambdas. Switch: `SEMANTEQ_NO_CONJUNCT_SURFACE`. -/
  conjunctSurface : Bool := true

/-- Record a failure reason. -/
def Ctx.fail (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.fails.modify (·.push r)

/-- Record a warning. -/
def Ctx.flag (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.flags.modify (·.push r)

/-- A severe use: recorded as `severe: …`; under `--strict` it also fails the
proof (the strict reading of the definition). -/
def Ctx.severe (ctx : Ctx) (msg : String) : MetaM Unit := do
  ctx.flag s!"severe: {msg}"
  if ctx.strictLocalProofs then ctx.fail s!"strict: severe use refused ({msg})"

/-- Does the local constant `c` reach `target` through local values? Never
looks inside the antecedent or the assumed set (their sorries are licensed;
they also must not launder reachability). -/
partial def constReaches (ctx : Ctx) (memo : IO.Ref (NameMap Bool))
    (target : Name) (c : Name) : MetaM Bool := do
  if let some b := (← memo.get).find? c then return b
  memo.modify (·.insert c false)  -- provisional false cuts cycles
  let mut out := false
  if c == target then
    out := true
  else if c == ctx.ante || ctx.assumed.contains c then
    out := false
  else if isLocalConst ctx.env c then
    if let some v := valueOf? ctx.env c (allowOpaque := true) then
      for c' in v.getUsedConstantsAsSet do
        if c' == target then out := true
        else if c' != ctx.ante && !ctx.assumed.contains c' && isLocalConst ctx.env c' then
          if ← constReaches ctx memo target c' then out := true
  memo.modify (·.insert c out)
  return out

/-- Does `e` involve the antecedent (constant mention, environment-local reach,
or an antecedent-involved local hypothesis)? Assumed theorems do not count. -/
def anteInvolved (ctx : Ctx) (e : Expr) : MetaM Bool := do
  let fvs ← ctx.anteFVars.get
  if e.hasAnyFVar (fvs.contains ·) then return true
  for c in e.getUsedConstantsAsSet do
    if c == ctx.ante then return true
    if isLocalConst ctx.env c then
      if ← constReaches ctx ctx.reachMemo ctx.ante c then return true
  return false

/-- Does `e` reach `sorryAx` other than through the antecedent or the assumed set? -/
def reachesSorry (ctx : Ctx) (e : Expr) : MetaM Bool := do
  for c in e.getUsedConstantsAsSet do
    if c == ``sorryAx then return true
    if c != ctx.ante && !ctx.assumed.contains c && isLocalConst ctx.env c then
      if ← constReaches ctx ctx.sorryMemo ``sorryAx c then return true
  return false

/-- Grade a statement expression: bridge-grade iff its conclusion head is Eq,
Iff, HEq or Ne, a class, a variable, or the whole statement is schematic. -/
def bridgeGradeType (env : Environment) (t : Expr) : MetaM Bool := do
  if schematicType t then return true
  bridgeConclusion env t

/-- Category of a global constant (memoized). Environment-local constants are
handled by family (`judgeOutsideLocal`, `expandLocal`), never here. -/
def categorize (ctx : Ctx) (c : Name) : MetaM Cat := do
  if c == ctx.ante then return .sanctioned
  if c == ``sorryAx then return .sorryC
  if exFalso5.contains c then return .exFalso
  if let some cat := (← ctx.catMemo.get).find? c then return cat
  let cat ← do
    -- eliminators are never bridge: their motive-headed conclusions would
    -- pass the variable-headed case of `bridgeConclusion`
    if ← isEliminatorConst ctx.env c then pure Cat.schematic
    else
    match ctx.env.find? c with
    | none => pure Cat.data
    | some info => do
      if !(← isPropSafe info.type) then
        pure Cat.data                     -- defs, structures, instances, recursors
      else if schematicType info.type then
        pure Cat.schematic
      else if ← bridgeConclusion ctx.env info.type then pure Cat.bridge
      else pure Cat.content
  ctx.catMemo.modify (·.insert c cat)
  return cat

/-- Record an occurrence of a local at a role; inside a record or a local
bridge's proof it goes to `recordOccRoles`. -/
def recordOcc (ctx : Ctx) (id : FVarId) (role : Role) : MetaM Unit := do
  let inRecord := (← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0
  let ref := if inRecord then ctx.recordOccRoles else ctx.occRoles
  ref.modify fun m => m.insert id ((m.get? id).map (Role.join role) |>.getD role)

/-- Used anywhere, plainly or inside a record? -/
def usedAnywhere (ctx : Ctx) (id : FVarId) : MetaM Bool := do
  return ((← ctx.occRoles.get).get? id).isSome || ((← ctx.recordOccRoles.get).get? id).isSome

/-- The carrier-affinity test: an antecedent application that instantiates a
`Sort`-valued parameter at a carrier sharing nothing with the goal statement
(no free variable of the proof context, no constant of the goal's type) uses
the antecedent off-subject as a generic schema while the real content
arrives through its value arguments. Native carriers (the goal's own types,
and the subtypes, products and images built from them) share vocabulary and
pass. -/
def foreignCarrier (ctx : Ctx) (t : Expr) : Bool :=
  if t.hasFVar then false          -- anchored to something in scope
  else if t.isSort then !ctx.goalPropCarrier  -- bare Prop/Sort instantiation
  else
    t.getUsedConstantsAsSet.all fun c =>
      coreLogicName c || !ctx.goalConsts.contains c

/-- `SEMANTEQ_AUDIT_TRACE`: log every constant grading decision. -/
def auditTrace : BaseIO Bool := return (← getConfig).auditTrace

/-- Judge one global constant under a role and polarity: the decision table. -/
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
    | .goal =>
      if (← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0 then
        -- a side condition of a conditional bridge inside a record, or a
        -- premise inside a local bridge's proof: tolerated and recorded
        ctx.flag s!"content import {c} inside a rewrite record or a local bridge's proof ({locus})"
      else ctx.fail s!"content import {c} on goal spine ({locus})"
    | .anteArg => ctx.flag s!"content import {c} feeding ante application ({locus})"
    | .side => pure ()
  | _ => pure ()

/-- Do the Iff/Eq sides of this statement unify with a goal part? Over-eager
matches (metavariable-assisted) are acceptable; this only flags. -/
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
        if ← withoutModifyingState (isDefEqSafe s p) then
          return true
    return false
  catch _ => return false

/-- An antecedent-free in-file lemma or a sorried assumption is an outside
lemma: its statement is graded at the use role and its proof is closed (the
sorry is licensed for the assumed). A bridge-graded statement gets the
goal-shaped check. -/
def judgeOutsideLocal (ctx : Ctx) (role : Role) (c : Name) : MetaM Unit := do
  let some info := ctx.env.find? c | return ()
  -- local vocabulary (defs, predicates, structures: non-Prop-typed) is data,
  -- the same exemption as the global non-Prop rule
  unless ← (isPropSafe info.type) do
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

/-- Look through an environment-local internal auxiliary or antecedent-involved
helper: judge every constant its value uses at the current role.
Antecedent-free user-named lemmas met inside are graded, not expanded. -/
partial def expandLocal (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) : MetaM Unit := do
  if ← auditTrace then IO.eprintln s!"[trace] expandLocal {c} @ {role.str} (seen={(← ctx.expanded.get).contains c})"
  if (← ctx.expanded.get).contains c then return ()
  ctx.expanded.modify (·.insert c)
  if let some v := valueOf? ctx.env c (allowOpaque := true) then
    for c' in v.getUsedConstantsAsSet do
      if c' == ctx.ante then continue
      if ctx.assumed.contains c' then judgeOutsideLocal ctx role c'
      else if isLocalConst ctx.env c' then
        if !c'.isInternalDetail && !(← constReaches ctx ctx.reachMemo ctx.ante c') then
          judgeOutsideLocal ctx role c'
        else expandLocal ctx role neg c'
      else judgeConst ctx role neg c' s!"via local {c}"
end ProofAudit
end SemantEq
