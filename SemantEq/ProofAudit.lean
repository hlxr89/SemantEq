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
* #5 goal-shaped local bridges are flagged,
* #6 the
  confiscated-instances reproof re-asserts the proof's own ante-free bindings
  wherever they sit — through case splits on goal hypotheses, intros and
  ante-free goal conversions — and refuses a proof whose branch goal then closes
  without the antecedent (`SEMANTEQ_NO_REPLAY_LOCAL_FACTS=1` restricts the
  collection to the leading have/let chain, for ablation),
* #7 the closed-witness audit: an antecedent existential hypothesis
  met with a witness that is neither built from a goal-side variable nor a
  closed term the goal statement mentions refuses the proof (`witnessAudit`;
  `SEMANTEQ_NO_WITNESS_CHECK=1` disables it, for ablation).

* #8 conjunct-level
  ablation: the components of `And.intro` / `Iff.intro` on the goal spine are goal
  parts, so an atomic or applicative component that closes ante-free
  (`⟨ante, rfl⟩`, `⟨ante, by decide⟩`) is refused like a branch that closes
  ante-free — a static dependency-cone test, no prover; not inside the converted
  proof of a conversion whose justification is ante-involved (the residual
  obligation after an antecedent-derived rewrite is not a goal part), nor in
  ANTE-ARG position (`SEMANTEQ_NO_CONJUNCT_ABLATION=1` disables it, for ablation).

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
  [``False.elim, ``False.rec, ``False.casesOn, ``absurd, ``Not.elim,
   -- eliminators of the other empty types prove
   -- anything without a `False` node
   ``Fin.elim0, ``Empty.elim, ``Empty.rec, ``PEmpty.elim, ``PEmpty.rec,
   `IsEmpty.elim, `IsEmpty.elim', `IsEmpty.false]

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
  (goal grants finiteness) from a manufactured instance (finiteness built
  from vacuous Prop hypotheses, not a goal binder). Computed from goalType so a
  `have`-minted Finite in the proof body cannot spoof it. -/
  goalHasFin : Bool := false
  occRoles   : IO.Ref (FVarIdMap Role)
  /-- occurrences INSIDE a rewrite record or a local bridge's
  proof, kept apart from the plain ones — a binding used only there is judged
  in the record regime (its value walked under `recordCtx`: content flags, a
  collapse convicts), not on the goal spine. -/
  recordOccRoles : IO.Ref (FVarIdMap Role)
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
  /-- #8 guard: depth of converted proofs under a conversion whose justification
  is ante-involved (`Eq.mpr`/`Eq.mp`/`Iff.mp`/`Iff.mpr`/`cast`, an `Eq.rec`
  substitution) — the goal is frozen there; a constructor's components are the
  residual obligation of the antecedent's rewrite, not goal parts -/
  frozenCtx : IO.Ref Nat
  /-- depth inside a rewrite/transition RECORD — the
  equation or biconditional a conversion rewrites along. Records are walked at
  the enclosing role (they used to be ancillary as a whole); a content constant
  met there is a flag, not a failure, since a conditional bridge's side
  condition may be met by any fact, while a goal part collapsed to `True` by a
  content fact inside a record is refused. -/
  recordCtx : IO.Ref Nat
  /-- depth inside the PROOF of an antecedent-free
  local bridge, read at the bridge's use role. Goal-part ablations are
  suspended there (the sub-proof proves the bridge, not the goal) and content
  is graded at the flag tier. -/
  localProofCtx : IO.Ref Nat
  /-- inline walks of an ante-involved in-file
  helper's body, per helper (capped, to bound repeated expansion). -/
  helperWalks : IO.Ref (NameMap Nat)
  /-- values of local data bindings (handleBinding introduces
  binding fvars valueless via withLocalDecl; the carrier rules must resolve
  a let-bound name to its value before the bare-surface test, or a
  `let X := <construction>` would slip past the carrier rules) -/
  localValues : IO.Ref (FVarIdMap Expr)
  /-- severe-warning tier: values of local Prop bindings (`have`), so a use of
  an outside fact can be tested for whether it draws on any local hypothesis
  through such a binding -/
  propValues : IO.Ref (FVarIdMap Expr)
  fails      : IO.Ref (Array String)
  flags      : IO.Ref (Array String)
  sorryHit   : IO.Ref Bool
  expanded   : IO.Ref NameSet             -- env-local consts already judged-through
  /-- #6: the reproof's collection looks through the proof's goal-side
  structure (case splits on goal hypotheses, intros, ante-free goal
  conversions) and re-asserts every ante-free local binding it meets before
  probing; `SEMANTEQ_NO_REPLAY_LOCAL_FACTS=1` restricts it to the leading
  have/let chain (ablation). -/
  replayLocalFacts : Bool := true
  /-- #7: audit the witnesses the proof supplies for the antecedent's
  existential hypotheses (`witnessAudit`); `SEMANTEQ_NO_WITNESS_CHECK=1`
  disables it (ablation). -/
  witnessCheck : Bool := true
  /-- the goal's closed statement (the witness audit's occurrence test) -/
  goalStmt : Expr := mkConst ``True
  /-- #8: ablate the components of `And.intro` / `Iff.intro` on the goal spine;
  `SEMANTEQ_NO_CONJUNCT_ABLATION=1` disables it (ablation). -/
  conjunctAblation : Bool := true
  /-- `--strict` / `SEMANTEQ_STRICT` : the STRICT READING of
  the definition as a mode. (a) A severe use — a library fact, or a local
  hypothesis proved from nothing local, meeting a hypothesis of the antecedent
  while drawing on no local hypothesis — FAILS the proof instead of being
  recorded; (b) the PROOFS of antecedent-free local bridges are
  also read at their use role, so a severe use hidden inside such a proof
  counts as well. Default off — the shape admission (RULE 2) and the tolerance
  are the shipped rules; strict adds to them, never replaces them. -/
  strictLocalProofs : Bool := false
  /-- a proof-typed lambda component of `And.intro` / `Iff.intro` /
  `Exists.intro` at goal role binds the goal statement's OWN objects (the ∀
  inside a conjunct), so its data binders draw on the surface budget like the
  goal's leading lambdas do. Switch: `SEMANTEQ_NO_CONJUNCT_SURFACE`. -/
  conjunctSurface : Bool := true

def Ctx.fail (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.fails.modify (·.push r)

def Ctx.flag (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.flags.modify (·.push r)

/-- A severe use: recorded as `severe: …`; under `--strict` it also fails the
proof (the strict reading of the definition). -/
def Ctx.severe (ctx : Ctx) (msg : String) : MetaM Unit := do
  ctx.flag s!"severe: {msg}"
  if ctx.strictLocalProofs then ctx.fail s!"strict: severe use refused ({msg})"

/-- Constant value with kernel-env fallback; 4.30 hides theorem values behind
`allowOpaque` : discipline of `RestrictedSearch.auditProof`). -/
def valueOf? (env : Environment) (c : Name) : Option Expr := do
  let info ← env.toKernelEnv.find? c <|> env.find? c
  info.value? (allowOpaque := true)

def isLocal (env : Environment) (c : Name) : Bool :=
  (env.getModuleIdxFor? c).isNone

/-- Does env-local constant `c` reach `target` through env-local values? Never
looks inside the ante or the assumed set (their sorries are licensed; they also
must not hide reachability; mirrors `Search.usesConstant`). -/
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
  tryCatchRuntimeEx (do return some (← inferType e)) (fun _ => return none)

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

def recordOcc (ctx : Ctx) (id : FVarId) (role : Role) : MetaM Unit := do
  let inRecord := (← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0
  let ref := if inRecord then ctx.recordOccRoles else ctx.occRoles
  ref.modify fun m => m.insert id ((m.get? id).map (Role.join role) |>.getD role)

/-- Used anywhere, plainly or inside a record? -/
def usedAnywhere (ctx : Ctx) (id : FVarId) : MetaM Bool := do
  return ((← ctx.occRoles.get).get? id).isSome || ((← ctx.recordOccRoles.get).get? id).isSome

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

/-- A switch: set to anything but empty / `0` / `false`. -/
def envFlag (name : String) : IO Bool := do
  match ← envVar name with
  | some v => return v != "" && v != "0" && v != "false"
  | none => return false
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
    | .goal =>
      if (← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0 then
        -- a side condition of a conditional bridge inside a record, or a
        -- premise inside a local bridge's proof: tolerated and recorded
        ctx.flag s!"content import {c} inside a rewrite record or a local bridge's proof ({locus})"
      else ctx.fail s!"content import {c} on goal spine ({locus})"
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
    else if let .const n _ := ty.getAppFn then
      -- an inhabitant of any constructor-less
      -- inductive (Empty, PEmpty) is a contradiction like `False`
      if let some (.inductInfo iv) := ctx.env.find? n then
        if iv.ctors.isEmpty then
          ctx.fail s!"constructs an inhabitant of the empty type {n} in positive position ({locus})"

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
      -- in disguise (derive `false = true` from the ante, prove anything)
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

/-- Entering a lambda whose body proves `False` = constructing a negation proof.
only when the binder is USED — `by_contra h` with `h`
never mentioned is `False.elim` in disguise, and keeps the outer polarity. -/
def negBump (body : Expr) (binderUsed : Bool := true) : MetaM Nat := do
  if !binderUsed then return 0
  match ← inferTypeSafe body with
  | some ty =>
    if ty.isConstOf ``False then return 1
    -- `Bool.noConfusion h : Bool.noConfusionType False false true` IS a proof of
    -- `False` (a statement concluding in a Bool `false`): reduce first
    let ty' ← try whnfD ty catch _ => pure ty
    return (if ty'.isConstOf ``False then 1 else 0)
  | none => return 0

/-- heads that collapse a proposition to `True` (or
drop a conjunct) on the strength of a proof of it — inside a rewrite record or
a local bridge's proof, the proof they consume is a goal part closed without
the antecedent when its cone is antecedent-free. -/
def collapseHead (c : Name) : Bool :=
  c == ``eq_true || c == ``iff_of_true || c == ``and_iff_left || c == ``and_iff_right ||
  c == ``iff_true_intro || c == `eq_true_intro || c == ``of_iff_true

/-- A definitional-equality test with a small heartbeat budget of its own, for
the guards that only need a cheap answer (`recordRewrites`, `isGoalSpineProp`);
a timeout counts as "not equal". -/
def isDefEqCheap (a b : Expr) : MetaM Bool := do
  withoutModifyingState do
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000000 }) do
      Core.withCurrHeartbeats do
        -- runtime exceptions (heartbeats, recursion depth) escape a plain
        -- `try … catch` in MetaM; a timeout is "not equal"
        tryCatchRuntimeEx (isDefEq a b) (fun _ => pure false)

/-- does this record actually rewrite? A justification
whose two sides coincide (`congrArg (fun _ => G) h : G = G`) transports nothing
and must not freeze the converted proof. -/
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

/-- Role-transition heads: `.mp`/`.mpr` conversions of the
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

/-- LOAD-BEARING involvement. A mention of the
antecedent that cannot carry its content into the part's conclusion — the
discarded argument of `Function.const`/`id`, a beta-redex's or `have`'s unused
binder, an unused `let`, any conversion/wrapper node whose type is `True` —
does not count (`⟨A, Function.const _ (by decide) A⟩` is a goal part closed
without the antecedent). Memoised on the term (proof terms from `omega` /
`nlinarith` are DAGs with heavy sharing; a tree walk explodes). Type inference
is limited to the conversion / wrapper heads that produce `True`-typed proofs
and to closed terms (under a binder the node is kept). -/
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
      if isLocal ctx.env c then constReaches ctx ctx.reachMemo ctx.ante c else return false
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
      -- a node whose
      -- TYPE is content-free — `True`, or a closed equation / biconditional
      -- whose two sides are definitionally equal (`decide P = true` for a
      -- closed decidable `P` evaluates to `true = true`) — carries nothing
      -- forward whatever it is built from; the antecedent passed through it
      -- is discarded by definitional evaluation. Tested at conversion heads,
      -- at heads whose conclusion is an equation, a biconditional, `True` or
      -- schematic (`Iff.mp`, `of_decide_eq_true`), and at projections.
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

/-- the propositions on the goal statement's PROPOSITIONAL SPINE —
the statement itself and everything reachable through ∧ / ↔ / ∨ / ¬, the body
of a ∀ / → and the body of an ∃. A proposition inside a term (an `if`
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
def isGoalSpineProp (ctx : Ctx) (p : Expr) : MetaM Bool := do
  -- the remaining CONCLUSION only: the goal's hypotheses (the peeled binders'
  -- types) are premises, not parts to be proved
  for q in spineParts (← ctx.goalTypeRem.get) do
    if matchWild q p then return true
    if !q.hasLooseBVars then
      if ← isDefEqCheap q p then return true
  return false

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

/-- Closed-witness audit, #7: the antecedent's existential hypothesis
`∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)` is met with the witness `0`, a closed term the
proof conjures, while the goal's own hypothesis `h : ∃ i : ℤ, …` already supplies
the corresponding object — an honest transport would witness with (a term built
from) `i`. At an application of the antecedent, every argument in an
existential-hypothesis slot that is an `Exists.intro` (possibly under casts, or
a `have`-bound name whose value is one) has its witness examined, nested `∃`s
included: a witness with no free variable of the proof context (let-bound names
resolved to their values first) that does not occur in the goal statement —
numerals compared literally — refuses the proof; so does a witness built only
from antecedent-derived variables (the walker's taint set). Witnesses mentioning
a goal-side variable (a goal parameter, a conclusion intro, a product of casing a
goal hypothesis), and closed terms the goal statement mentions, pass.
`SEMANTEQ_NO_WITNESS_CHECK=1` disables the audit (ablation). -/
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
      -- built from the goal = mentions a goal-side variable: any free variable
      -- of the proof context that is NOT tainted (the walker's `anteFVars`:
      -- bindings with ante-involved values and the products of destructuring
      -- ante-derived facts). Goal parameters, conclusion intros and the
      -- products of casing a GOAL hypothesis all qualify.
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

/-- Severe tier of the ante-argument warning. Traverse `e`, looking
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

/-- Inside a rewrite record or a local bridge's proof, positional goal-part
ablations are suspended (the sub-proof proves the record or the bridge, not
the goal); only the collapse rules convict there. -/
def ablationSuspended (ctx : Ctx) : MetaM Bool := do
  return (← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0

/-- inside a record or a local
bridge's proof, an antecedent-free proof of `p = True` / `p ↔ True` for a goal
spine part `p` is a goal part closed without the antecedent, whatever head
built it (`if_pos`, `decide_eq_true`, a `_simp_N` auxiliary, `propext …`). -/
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

/-- If judging the head `c` just raised an ante-argument content warning, add
the severe tier when the whole application draws on no local proposition. -/
def severeIfClosed (ctx : Ctx) (nBefore : Nat) (c : Name) (args : Array Expr) : MetaM Unit := do
  let flags ← ctx.flags.get
  let fresh := flags.extract nBefore flags.size
  unless fresh.any (fun s => (s.splitOn "feeding ante application").length > 1) do return ()
  let (prop, data) ← localityOf ctx (mkAppN (.const c []) args)
  unless prop do
    let note := if data then "" else ", nor on any local variable"
    ctx.severe s!"outside fact {c} feeding ante application draws on no local hypothesis{note}"

mutual

partial def walkLam (ctx : Ctx) (role : Role) (neg : Nat) (bindersAnte : Bool)
    : Expr → MetaM Unit
  | .lam n t b bi => do
    withLocalDecl n bi t fun x => do
      if bindersAnte then ctx.anteFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body (b.hasLooseBVar 0))
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
      let neg' := neg + (← negBump body (b.hasLooseBVar 0))
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
      let neg' := neg + (← negBump body (b.hasLooseBVar 0))
      walkLamSurface ctx role neg' body
  | .letE n t v b _ =>
    -- surface passthrough: the goal's own binders may be intro'd AFTER
    -- have/let steps; the peeler continues through bindings so the budget
    -- reaches them (putnam_1999_a6 / 2008_b4 class)
    handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default, b.hasLooseBVar 0⟩ true
  | e => do
    if let some bind := asBinding? e then handleBinding ctx role neg bind true
    else walk ctx role neg e

partial def walk (ctx : Ctx) (role : Role) (neg : Nat) (e : Expr) : MetaM Unit := do
  match e with
  | .bvar _ | .mvar _ | .sort _ | .lit _ => pure ()
  | .fvar id =>
    recordOcc ctx id role
    checkFalseNode ctx neg e "hypothesis of type False"
  | .const c us => do
    let nFlagsBefore := (← ctx.flags.get).size
    if c == ctx.ante then pure ()
    else if ctx.assumed.contains c then judgeOutsideLocal ctx role c
    else if isLocal ctx.env c then
      if c.isInternalDetail && !(← ablationSuspended ctx) then expandLocal ctx role neg c
      else if c.isInternalDetail || (← constReaches ctx ctx.reachMemo ctx.ante c) then
        -- inline walk of the helper's body (capped)
        let n := ((← ctx.helperWalks.get).find? c).getD 0
        match (if n < 2 then valueOf? ctx.env c else none), ctx.env.find? c with
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
        -- a `noConfusion`-family discriminator on a
        -- DERIVED equation (not a bare case binder) proves anything from an
        -- absurd equation without a `False` node — ex falso at positive polarity
        if neg == 0 && nameHasNoConfusion c && !isLocal ctx.env c then
          unless ← benignNoConfusionFalse ctx e do
            ctx.fail s!"explosion through {c} on a derived equation in positive position"
        -- head judging, by family (#3/#4)
        let isAss := ctx.assumed.contains c
        let isLoc := !isAss && c != ctx.ante && isLocal ctx.env c
        let locInternal := isLoc && c.isInternalDetail
        let locInvolved ← if isLoc && !locInternal then
            constReaches ctx ctx.reachMemo ctx.ante c
          else pure false
        let isLocFree := isLoc && !locInternal && !locInvolved
        -- an ante-involved in-file helper (theorem /
        -- def / instance) is walked INLINE, its body instantiated at the call's
        -- arguments, at the call's role and polarity — so the conjunct
        -- ablation, the witness audit and the polarity rules reach inside it.
        -- Capped per helper; beyond the cap the constant grading stands in.
        -- Internal auxiliaries (`_simp_N`, `_proof_N`) are read inline too
        -- when they sit inside a record or a local bridge's proof: the collapse
        -- heads inside them (`_simp_1 := eq_true X`) are what convicts there.
        if locInvolved || (locInternal && (← ablationSuspended ctx)) then
          let n := ((← ctx.helperWalks.get).find? c).getD 0
          if n < 2 then
            if let some info := ctx.env.find? c then
              if let some v := valueOf? ctx.env c then
                let us := match f with | .const _ us => us | _ => []
                let v := v.instantiateLevelParams info.levelParams us
                ctx.helperWalks.modify (·.insert c (n+1))
                if ← auditTrace then IO.eprintln s!"[trace] inline walk of helper {c} @ {role.str}"
                -- the residual lambdas prove the goal part at this position,
                -- so at goal role their binders are the goal's own objects
                let body := (mkAppN v args).headBeta
                if role == .goal then walkLamSurface ctx role neg body
                else walk ctx role neg body
                return
        let nFlagsBefore := (← ctx.flags.get).size
        if c == ctx.ante then pure ()
        else if isAss || isLocFree then
          judgeOutsideLocal ctx role c
          -- a bridge-shaped ante-free in-file lemma
          -- keeps its shape admission, and its proof is read once at the use role
          if isLocFree && role != .side then walkOutsideLocalProof ctx role neg c
        else if isLoc then expandLocal ctx role neg c
        else judgeConst ctx role neg c "application head"
        if role == .anteArg then severeIfClosed ctx nFlagsBefore c args
        -- a goal part collapsed to `True` (or a
        -- conjunct dropped) by a content fact inside a record or a local
        -- bridge's proof is a goal part closed without the antecedent
        if role == .goal && collapseHead c
            && ((← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0) then
          for a in args do
            collapseAblation ctx a s!"goal part collapsed by {c} inside a rewrite record or a local bridge's proof" (spine := true)
        -- #8 conjunct-level ablation: at GOAL role the components of `And.intro`
        -- / `Iff.intro` are goal parts, so an atomic or applicative component
        -- (`rfl`, a `decide` term, a goal hypothesis) that closes ante-free is
        -- a redundant goal part — the D2 relevance pair, `⟨ante, rfl⟩`. Lambda
        -- components are ablated by the generic arm below already. Static:
        -- `branchAblation`'s dependency-cone test, no prover. Guard: not under
        -- a conversion justified by the antecedent (`frozenCtx`; `apply ante.2`
        -- then `⟨hn, hk, _⟩`, or `rw [ante]` then `⟨x.1.2, x.2.2⟩` — the
        -- antecedent's premises / residual obligation, not goal parts); ANTE-ARG
        -- position is excluded by the role.
        if ctx.conjunctAblation && role == .goal && (← ctx.frozenCtx.get) == 0
            && !(← ablationSuspended ctx) && (c == ``And.intro || c == ``Iff.intro) then
          for a in args do
            unless a.isLambda do
              branchAblation ctx a s!"constructor component ({c})"
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
                  --     (a TopologicalSpace slot filled with ⊤). The
                  --     substitution changes meaning because the class is not a
                  --     subsingleton.
                  --   (ii)  SUBSINGLETON but content-bearing (Fintype) manufactured
                  --     when the goal statement grants no such structure (a
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
                    -- a Sort-valued surface slot
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
                      -- IS the goal's own object (`↥F` occurring inside
                      -- `IsAlgebraic F a`, say)
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
          -- #7: closed-witness audit of the ante's existential hypotheses
          if c == ctx.ante && ctx.witnessCheck then
            if let some info := ctx.env.find? c then
              witnessAudit ctx info.type args
          -- the ante, or an ante-involved local lemma: its arguments feed the
          -- ante pipeline
          for a in args do walk ctx .anteArg neg a
        else if transitionHead c then
          -- the role-transition rule : a transition transports
          -- the ROLE with the content — the converted proof (last arg) inherits
          -- the conversion's position. the RECORD (the
          -- equation/iff being used, second-to-last arg) is no longer ancillary
          -- as a whole: it walks at the enclosing role inside `recordCtx`, where
          -- content is a flag and a collapsed goal part is refused.
          ctx.chainCtx.modify (·+1)
          -- #8 guard: an ante-involved justification that actually rewrites
          -- freezes the converted proof
          let recInv ← if args.size ≥ 2 then
              (do if ← anteInvolved ctx args[args.size - 2]! then recordRewrites args[args.size - 2]! else pure false)
            else pure false
          for i in [0:args.size] do
            if args.size ≥ 2 && i == args.size - 2 then
              ctx.recordCtx.modify (·+1)
              walk ctx role neg args[i]!
              ctx.recordCtx.modify (·-1)
            else if recInv && i == args.size - 1 then
              ctx.frozenCtx.modify (·+1)
              walk ctx role neg args[i]!
              ctx.frozenCtx.modify (·-1)
            else walk ctx role neg args[i]!
          ctx.chainCtx.modify (·-1)
        else if recordHead c then
          ctx.chainCtx.modify (·+1)
          for i in [0:args.size] do
            if i == args.size - 1 then
              ctx.recordCtx.modify (·+1)
              walk ctx role neg args[i]!
              ctx.recordCtx.modify (·-1)
            else walk ctx role neg args[i]!
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
          -- #8 guard: a substitution along an ante-involved equation that
          -- actually rewrites freezes its minor (the goal
          -- transported by the antecedent's rewrite)
          let mut majorRewrites := true
          if eqRecFamily c && majorInv then
            for a in args do
              if !a.isLambda then
                if (← isProofSafe a) && (← anteInvolved ctx a) then
                  majorRewrites ← recordRewrites a
          let eqFrozen := eqRecFamily c && majorInv && majorRewrites
          if eqFrozen then ctx.frozenCtx.modify (·+1)
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
          -- content — the `Set.center_prod` class
          -- not inside a record / a local bridge's proof either: a value walked
          -- there (omega's `_proof_N` auxiliaries in the proof of an equation
          -- used by `rw`) applies equations bare without asserting them as goal
          -- content
          if role == .goal && (← ctx.chainCtx.get) == 0 && !isLoc && !isAss
              && !(← ablationSuspended ctx) then
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
          -- #8 guard: `cast` along an ante-involved equation that actually
          -- rewrites freezes its value
          let castFrozen ← if c == ``cast && args.size == 4 then
              (do if ← anteInvolved ctx args[2]! then recordRewrites args[2]! else pure false)
            else pure false
          let ctorHead := c == ``And.intro || c == ``Iff.intro || c == ``Exists.intro
          for i in [0:args.size] do
            let a := args[i]!
            if castFrozen && i == 3 then
              ctx.frozenCtx.modify (·+1)
              walk ctx role neg a
              ctx.frozenCtx.modify (·-1)
            else if ctx.conjunctSurface && role == .goal && ctorHead && a.isLambda
                && (← isProofSafe a) then
              -- `⟨…, fun n => A n⟩` — the component's binders are
              -- the goal statement's own quantified objects (budgeted)
              walkLamSurface ctx role neg a
            else walk ctx role neg a
            if role == .goal && a.isLambda && !dataHead then
              branchAblation ctx a "lambda argument"
          if c == ``cast then ctx.chainCtx.modify (·-1)
      | .fvar id =>
        recordOcc ctx id role
        let anteHead := (← ctx.anteFVars.get).contains id
        for a in args do
          walk ctx (if anteHead then .anteArg else role) neg a
      | .proj sName _ s =>
        -- Iff/Eq projections are TRANSITIONS: the record walks at the
        -- enclosing role inside `recordCtx` , the converted proof
        -- inherits the role; other projections keep clause B
        checkFalseNode ctx neg f "projection"
        if sName == ``Iff || sName == ``Eq then
          ctx.chainCtx.modify (·+1)
          ctx.recordCtx.modify (·+1)
          walk ctx role neg s
          ctx.recordCtx.modify (·-1)
          -- #8 guard: an ante-involved record that rewrites freezes the converted proofs
          let recInv ← (do if ← anteInvolved ctx s then recordRewrites s else pure false)
          if recInv then ctx.frozenCtx.modify (·+1)
          for a in args do walk ctx role neg a
          if recInv then ctx.frozenCtx.modify (·-1)
          ctx.chainCtx.modify (·-1)
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
  -- inside a rewrite record (a conditional bridge's side
  -- conditions, a `forall_congr` pointwise lambda) or a local bridge's proof
  -- the sub-proof proves the record / the bridge, not the goal — positional
  -- goal-part ablation is suspended there; only the collapse heads convict
  if ← ablationSuspended ctx then return ()
  collapseAblation ctx a locus

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

/-- Read the PROOF of a bridge-shaped, antecedent-free in-file
lemma once, at the role where the lemma is used, with goal-part ablations
suspended and content at the flag tier (the shape admission stays the floor). -/
partial def walkOutsideLocalProof (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) : MetaM Unit := do
  unless ctx.strictLocalProofs do return ()
  unless ((← ctx.localGrade.get).find? c).getD false do return ()
  let n := ((← ctx.helperWalks.get).find? c).getD 0
  if n ≥ 1 then return ()
  let some info := ctx.env.find? c | return ()
  let some v := valueOf? ctx.env c | return ()
  if v.getUsedConstantsAsSet.contains ``sorryAx then return ()
  ctx.helperWalks.modify (·.insert c (n+1))
  ctx.localProofCtx.modify (·+1)
  walk ctx role neg (v.instantiateLevelParams info.levelParams [])
  ctx.localProofCtx.modify (·-1)

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
    -- a binding used ONLY inside records / local bridge proofs is judged in
    -- that regime — its value is walked at the record's role under `recordCtx`
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
      -- RULE 2: ante-free Prop local = outside lemma; sorry scan on the value.
      if ← auditTrace then do
        let jrs := (jr.map Role.str).getD "unused"
        IO.eprintln s!"[trace] RULE2 have {b.binderName} jr={jrs}"
      if ← reachesSorry ctx b.value then ctx.sorryHit.set true
      if ← bridgeGradeType ctx.env b.binderType then
        -- local bridge admitted — flag if it quotes the goal
        if ← goalShaped ctx b.binderType then
          ctx.flag s!"goal-shaped local bridge (have {b.binderName})"
        -- the shape admission is the floor; the
        -- bridge's PROOF is now read at its use role, with goal-part ablations
        -- suspended (it proves the bridge, not the goal) and content at the
        -- flag tier, while a goal part collapsed inside it is refused
        match jr.orElse (fun _ => jrRec) with
        | some r =>
          if ctx.strictLocalProofs && r != .side then
            ctx.localProofCtx.modify (·+1)
            walk ctx r neg b.value
            ctx.localProofCtx.modify (·-1)
        | none => pure ()
      else
        match jr with
        | some .goal =>
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

def computeGoalParts (goalType : Expr) : MetaM (Array Expr) := do
  try
    let (_, _, concl) ← forallMetaTelescope goalType
    return splitAnd concl
  catch _ => return #[]

/-- Differential reproof outcome : the armed probe's
success has two causes the single probe conflated — the confiscated
constructions enabled the ante-free close (middleman → convict), or the goal
was provable bare (a property of the pair, not of the proof: never convicted,
and since not reported either). -/
inductive ReproofOutcome | silent | middleman | bareProvable
deriving BEq

/-- Per-direction state of the reproof's extended collection (#6) — the outer
conclusion and the pristine telescope context
(fallback target of the bare probe), the leaf budget, and the aggregate outcome
(middleman dominates bare-provable dominates silent). -/
structure DeepReplay where
  concl     : Expr
  baseLCtx  : LocalContext
  baseInsts : LocalInstances
  leaves    : IO.Ref Nat
  outcome   : IO.Ref ReproofOutcome

/-- At most this many leaf probes per direction in the extended collection
(each leaf costs an `assumption` + `exact?` attempt; case splits multiply
leaves). -/
def deepReplayLeafBudget : Nat := 4

/-- Confiscated-instances reproof: on an otherwise-PASSing
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
library-provable outright — no implication proof can witness or hide
anything there; not convicted, and not reported (the fact says nothing about
the proof under audit).

Extended collection (#6): the leading-chain collection
above misses a fact bound under a case split on a goal hypothesis (`rcases h
with ⟨i, hi⟩` wraps the rest of the proof in a minor premise). When it is silent,
`deep` walks the proof's goal-side structure, re-asserts every ante-free binding
it meets (transitively: nothing that reaches the antecedent) and runs the same
differential probe on each branch goal (`SEMANTEQ_NO_REPLAY_LOCAL_FACTS=1`
switches this off, for ablation). -/
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
      let baseline ← do
        if !(← collect concl body) then pure ReproofOutcome.silent
        else if ← probe concl then pure .bareProvable
        else pure .middleman
      if !ctx.replayLocalFacts || baseline != .silent then return baseline
      -- the leading-chain collection has spoken first (its verdicts stand — a
      -- bare-provable conclusion is never a conviction); on a silent direction
      -- the extended collection walks the proof and probes its branch goals
      let dr : DeepReplay := {
        concl, baseLCtx := ← getLCtx, baseInsts := ← getLocalInstances
        leaves := ← IO.mkRef 0, outcome := ← IO.mkRef .silent }
      deep dr concl {} {} false false body
      return ← dr.outcome.get
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
  /-- The extended collection (#6; the rule, probe the goal with
  every locally defined instance and every ante-free local lemma re-asserted,
  wherever it sits in the proof term). It re-asserts ante-free
  bindings by value exactly as `collect`, but walks the whole GOAL-SIDE
  structure of the proof — `intro` lambdas, `Eq.mpr`/`Eq.mp` goal conversions,
  and the minor premises of eliminations / `match`es (`rcases h with ⟨i, hi⟩`
  on a goal hypothesis wraps the rest of the proof in a minor premise, which is
  where such a `have` typically lives) — and probes each branch goal
  at its leaves. Bound variables are introduced as goal-side fvars, visible to
  both probes. Ante-freeness is TRANSITIVE: a binding whose type or value
  reaches the antecedent, or mentions a tainted fvar, is introduced OPAQUE and
  tainted (`tainted`), never re-asserted; the products of an elimination whose
  discriminant is tainted are tainted. The probed goal is refined only through
  untainted structure (an ante-derived rewrite or destructuring keeps the
  enclosing goal — closing the ante-derived reformulation is honest).
  `armed` collects the fvars only the armed probe may see. -/
  deep (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed frozen : Bool)
      (e : Expr)
      : Term.TermElabM Unit := do
    if (← dr.outcome.get) == .middleman then return ()
    let taints (x : Expr) : Bool := x.hasAnyFVar tainted.contains
    match asBinding? e with
    | some b =>
      if taints b.binderType || taints b.value || (← anteInvolved ctx b.binderType)
          || (← anteInvolved ctx b.value) then
        -- ante-involved (transitively): opaque, tainted, never re-asserted
        Meta.withLocalDecl b.binderName b.binderInfo b.binderType fun x =>
          deep dr goal (tainted.insert x.fvarId!) armed viaArmed frozen (b.mkBody x)
      else
        Meta.withLetDecl b.binderName b.binderType b.value fun x => do
          if ← auditTrace then
            IO.eprintln s!"[trace] replay re-asserts {b.binderName} : {← Meta.ppExpr b.binderType}"
          let k := deep dr goal tainted (armed.insert x.fvarId!) viaArmed frozen (b.mkBody x)
          match ← try Meta.isClass? b.binderType catch _ => pure none with
          | some cls => Meta.withNewLocalInstance cls x k
          | none => k
    | none =>
      match e with
      | .mdata _ b => deep dr goal tainted armed viaArmed frozen b
      | .lam .. => deepLam dr goal tainted armed viaArmed frozen frozen e
      | .app .. =>
        let args := e.getAppArgs
        match e.getAppFn with
        | .const c _ =>
          if (c == ``Eq.mpr || c == ``Eq.mp) && args.size == 4 then
            -- goal conversion: with an ante-free record the converted proof
            -- proves the other side, which becomes the goal; with an
            -- ante-derived record the enclosing goal stands
            let record := args[2]!
            let refine := !frozen && !(taints record || (← anteInvolved ctx record))
            let goal' := if refine then (if c == ``Eq.mpr then args[1]! else args[0]!).headBeta
              else goal
            -- a goal refined THROUGH a re-asserted fact carries that fact's power
            -- into its statement; only the pristine outer conclusion is bare then
            let viaArmed' := viaArmed || (refine && record.hasAnyFVar armed.contains)
            -- an ante-derived conversion FREEZES the goal for the rest of the path:
            -- everything beneath proves the ante-rewritten goal, so later
            -- refinements would be relative to a statement that embeds the ante
            deep dr goal' tainted armed viaArmed' (frozen || !refine) args[3]!
          else if (← isEliminatorConst ctx.env c) || isMatcherCore ctx.env c then
            -- the minor premises each prove a branch goal (read off the
            -- eliminator's own type — the reproof runs in the pristine import
            -- env, where type inference over the proof body can fail on
            -- fixture-local auxiliaries); their products are tainted iff a
            -- discriminant / the major is
            let minors ← elimMinors c args
            let mut dirty := false
            let mut armedDisc := false
            for i in [0:args.size] do
              if (minors.find? (·.1 == i)).isNone then
                let a := args[i]!
                if taints a || (← anteInvolved ctx a) then dirty := true
                if a.hasAnyFVar armed.contains then armedDisc := true
            -- a frozen goal stays frozen: the branch goals beneath are relative
            -- to the ante-rewritten statement
            let keep := dirty || frozen
            if minors.isEmpty then deepLeaf dr goal tainted armed viaArmed e
            else
              for (i, ty) in minors do
                let goal' := if keep then goal else ty.headBeta
                -- a `subst`/`cases` on a re-asserted fact refines the branch goal
                -- through that fact (0174: `subst a` with `ha0 : a = 0`)
                let viaArmed' := viaArmed || (!keep && armedDisc)
                deepLam dr goal' tainted armed viaArmed' keep keep args[i]!
          else deepLeaf dr goal tainted armed viaArmed e
        | _ => deepLeaf dr goal tainted armed viaArmed e
      | _ => deepLeaf dr goal tainted armed viaArmed e
  /-- The minor premises of an eliminator / matcher application —
  argument positions whose binder type (in the constant's telescope) concludes
  in a parameter-headed application (`motive ⟨w, h⟩`, `c` of `Or.elim`) — with
  the expected type of each, instantiated at the actual arguments. Read from
  the fixture env (matchers are fixture-local); empty on any failure. -/
  elimMinors (c : Name) (args : Array Expr) : Term.TermElabM (Array (Nat × Expr)) := do
    let some info := ctx.env.find? c | return #[]
    try
      forallBoundedTelescope info.type args.size fun params _ => do
        let mut out := #[]
        for i in [0:min params.size args.size] do
          let ty ← inferType params[i]!
          let isMinor ← forallTelescope ty fun _ concl =>
            pure (match concl.getAppFn with
              | .fvar id => params.any (·.fvarId! == id)
              | _ => false)
          if isMinor then
            out := out.push (i, ty.replaceFVars params[0:i] args[0:i])
        return out
    catch _ => return #[]
  /-- Peel a lambda chain (an `intro`, or a minor premise's products),
  introducing each binder as a goal-side fvar — tainted when `taint` (products
  of an ante-derived destructuring) or when its type mentions a tainted fvar.
  The goal loses one Pi per binder while it has one to lose; under a tainted
  destructuring or a frozen goal the enclosing goal is kept. -/
  deepLam (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed frozen taint : Bool)
      : Expr → Term.TermElabM Unit
    | .lam n t b bi =>
      Meta.withLocalDecl n bi t fun x => do
        let body := b.instantiate1 x
        let tainted' := if taint || t.hasAnyFVar tainted.contains then tainted.insert x.fvarId!
          else tainted
        let goal' ← do
          if taint then pure (some goal)
          else
            let g ← if goal.isForall then pure goal
              else try whnf goal catch _ => pure goal
            match g with
            | .forallE _ _ gb _ => pure (some (gb.instantiate1 x).headBeta)
            | _ => pure ((← inferTypeSafe body).map (·.headBeta))
        -- no goal to track (inference failed in the pristine env): stop here
        if let some goal' := goal' then deepLam dr goal' tainted' armed viaArmed frozen taint body
    | e => deep dr goal tainted armed viaArmed frozen e
  /-- A leaf of the extended collection: budgeted; `letI`-inlined instances of the terminal
  application are confiscated as in `inline`, then the branch goal is probed. -/
  deepLeaf (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed : Bool)
      (e : Expr)
      : Term.TermElabM Unit := do
    if goal.hasAnyFVar tainted.contains then return ()  -- no honest goal to probe here
    if (← dr.leaves.get) ≥ deepReplayLeafBudget then return ()
    dr.leaves.modify (· + 1)
    deepInline dr goal.headBeta tainted armed viaArmed e.getAppArgs 0
  deepInline (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed : Bool)
      (args : Array Expr) (i : Nat) : Term.TermElabM Unit := do
    if h : i < args.size then
      let a := args[i]
      let take ← do
        if a.isFVar || a.hasAnyFVar tainted.contains then pure none
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
          Meta.withNewLocalInstance cls x <|
            deepInline dr goal tainted (armed.insert x.fvarId!) viaArmed args (i+1)
      | none => deepInline dr goal tainted armed viaArmed args (i+1)
    else
      deepProbe dr goal tainted armed viaArmed
  /-- Differential probe at a leaf — the weak prover and the differential logic
  of the leading-chain replay. Armed: the branch goal, the goal-side
  binders and every re-asserted binding (tainted binders cleared — they are
  dependency-closed by construction). Bare: the same with the re-asserted
  bindings cleared too (when the goal or a remaining binder depends on one, or
  the goal was refined through one, the baseline's bare probe — the pristine
  outer conclusion — stands in).
  Middleman at any leaf refuses the direction through the baseline's path;
  bare success is recorded as bare-provable and not reported. -/
  deepProbe (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed : Bool)
      : Term.TermElabM Unit := do
    let trace ← auditTrace
    if trace then
      IO.eprintln s!"[trace] replay probes {← Meta.ppExpr goal} with {armed.size} re-asserted binding(s), {tainted.size} tainted"
    -- `withErasedFVars` (not a hand-rolled erase): a class-typed let-decl is
    -- registered as a local instance by `withLetDecl` AND by the explicit
    -- `withNewLocalInstance`; erasing one entry leaves a dangling instance that
    -- `exact?` then builds an unassignable proof from (measured )
    -- a Pi goal (an eliminator's motive, the ante's `∀ a b` conclusion) is
    -- opened first: `exact?` finds a proof of a Pi but cannot replay its own
    -- suggestion (it names the intro'd hypothesis), so the prover — unchanged —
    -- must see the conclusion, as it does for the baseline's `concl`
    Meta.withErasedFVars tainted.toList.toArray <| forallTelescope goal fun _ goal => do
      unless ← probe goal do return ()
      let touches (x : Expr) : Bool := x.hasAnyFVar armed.contains
      let dependent := touches goal || (← getLCtx).any fun d =>
        !armed.contains d.fvarId && (touches d.type || (d.value?.map touches).getD false)
      let bareLeaf ← if dependent || viaArmed then pure false
        else Meta.withErasedFVars armed.toList.toArray (probe goal)
      -- the baseline's own bare probe (pristine outer conclusion) as the second
      -- opinion: a branch goal refined through intros / ante-free rewrites can
      -- miss the library proof the outer conclusion has, and a bare-provable
      -- conclusion is never a conviction
      let bare ← if bareLeaf then pure true
        else Meta.withLCtx dr.baseLCtx dr.baseInsts (probe dr.concl)
      if trace then
        IO.eprintln s!"[trace] replay armed probe closed; bare probe {if bare then "closed (bare-provable)" else "failed (middleman)"}"
      if bare then
        if (← dr.outcome.get) == .silent then dr.outcome.set .bareProvable
      else dr.outcome.set .middleman

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
`--raw` prints the JSON record instead). Readable report: verdict, the reasons of a FAIL, then the warnings — the
ordinary tolerated uses as counts by kind, every severe warning in full, and
any axiom beyond the three standard ones. -/
def FixtureResult.render (r : FixtureResult) : String := Id.run do
  let mut out := s!"── {r.file}\n   verdict: {r.verdict}"
  if r.ante != .anonymous then out := out ++ s!"   (antecedent {r.ante}, goal {r.goal})"
  out := out ++ "\n"
  if r.verdict != "PASS" then
    if r.reasons.isEmpty then
      if r.verdict == "FAIL" then out := out ++ "   reasons: none recorded\n"
    else
      out := out ++ "   reasons:\n"
      for x in r.reasons do out := out ++ s!"      {x}\n"
  if r.verdict == "PASS" || r.verdict == "FAIL" then
    let severe := r.flags.filter (·.startsWith "severe: ")
    let axioms := r.flags.filter (·.startsWith "axiom ")
    let plain := r.flags.filter fun x => !(x.startsWith "severe: ") && !(x.startsWith "axiom ")
    -- counts by kind
    let isLib (x : String) := x.startsWith "content import" && (x.splitOn "feeding ante application").length > 1
    let isLoc (x : String) := (x.startsWith "bare-Prop local hypothesis" || x.startsWith "content-graded local fact")
                              && (x.splitOn "feeding ante application").length > 1
    let isRec (x : String) := (x.splitOn "inside a rewrite record").length > 1
    let isShape (x : String) := x.startsWith "goal-shaped local bridge"
    let nLib := (plain.filter isLib).size
    let nLoc := (plain.filter isLoc).size
    let nRec := (plain.filter isRec).size
    let nShape := (plain.filter isShape).size
    let nOther := plain.size - nLib - nLoc - nRec - nShape
    if plain.isEmpty then out := out ++ "   warnings: none\n"
    else
      let mut parts : Array String := #[]
      if nLib > 0 then parts := parts.push s!"{nLib} library fact{if nLib == 1 then "" else "s"} meeting a hypothesis of the antecedent"
      if nLoc > 0 then parts := parts.push s!"{nLoc} local hypothes{if nLoc == 1 then "is" else "es"} meeting a hypothesis of the antecedent"
      if nRec > 0 then parts := parts.push s!"{nRec} library fact{if nRec == 1 then "" else "s"} inside a rewrite record or a local restatement's proof"
      if nShape > 0 then parts := parts.push s!"{nShape} goal-shaped local restatement{if nShape == 1 then "" else "s"}"
      if nOther > 0 then parts := parts.push s!"{nOther} other"
      out := out ++ s!"   warnings: {plain.size} tolerated ({", ".intercalate parts.toList})\n"
    if severe.isEmpty then out := out ++ "   severe warnings: none\n"
    else
      out := out ++ s!"   severe warnings: {severe.size}\n"
      -- identical messages grouped, in first-occurrence order
      let mut seen : Array (String × Nat) := #[]
      for x in severe do
        let m := (x.drop 8).copy
        match seen.findIdx? (·.1 == m) with
        | some i => seen := seen.modify i fun (k, n) => (k, n + 1)
        | none => seen := seen.push (m, 1)
      for (m, n) in seen do
        out := out ++ s!"      {m}{if n > 1 then s!"   (×{n})" else ""}\n"
    if axioms.isEmpty then out := out ++ "   axioms beyond propext, Classical.choice, Quot.sound: none\n"
    else
      out := out ++ "   axioms beyond propext, Classical.choice, Quot.sound:\n"
      for x in axioms do
        let note := if (x.splitOn "native_decide").length > 1 then "   (native_decide)" else ""
        out := out ++ s!"      {x.drop 6}{note}\n"
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
def auditFixture (path : String) (strict : Bool := false) : IO FixtureResult := do
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
    replayLocalFacts := !(← envFlag "NO_REPLAY_LOCAL_FACTS")
    witnessCheck := !(← envFlag "NO_WITNESS_CHECK")
    conjunctAblation := !(← envFlag "NO_CONJUNCT_ABLATION")
    strictLocalProofs := strict || (← envFlag "STRICT")
    conjunctSurface := !(← envFlag "NO_CONJUNCT_SURFACE")
    goalStmt := goalType
    catMemo := ← IO.mkRef {}, reachMemo := ← IO.mkRef {}, sorryMemo := ← IO.mkRef {}
    localGrade := ← IO.mkRef {}, goalParts := ← IO.mkRef #[]
    occRoles := ← IO.mkRef {}, recordOccRoles := ← IO.mkRef {}, anteFVars := ← IO.mkRef {}
    surfaceFVars := ← IO.mkRef {}, surfaceLeft := ← IO.mkRef 0
    anteSlotData := ← IO.mkRef #[], localValues := ← IO.mkRef {}
    propValues := ← IO.mkRef {}
    chainCtx := ← IO.mkRef 0, frozenCtx := ← IO.mkRef 0
    recordCtx := ← IO.mkRef 0, localProofCtx := ← IO.mkRef 0, helperWalks := ← IO.mkRef {}
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
        if !(← anteInvolvedLB ctx goalVal) then
          ctx.fail "proof never touches the antecedent"
        walkLamSurface ctx .goal 0 goalVal
        -- axiom accounting. The three standard axioms and
        -- `sorryAx` (the assumed statements are sorried by protocol) are
        -- expected; anything else — a local `axiom`, `Lean.ofReduceBool` from
        -- `native_decide`, … — is reported by name.
        for a in (← Lean.collectAxioms goal) do
          if a == ``propext || a == ``Classical.choice || a == ``Quot.sound || a == ``sorryAx then
            continue
          let here := if isLocal ctx.env a then " (declared in this file)" else ""
          ctx.flag s!"axiom {a} used by the proof{here}"
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
    -- a bare-provable conclusion (the goal closes from the library alone) is a
    -- property of the pair, not of this proof, and is neither a conviction nor a
    -- report (the former "library-true" flag was removed)
    if outcome == .middleman then
      fails := fails.push
        "goal provable without the antecedent given the proof's own ante-free \
         local constructions (confiscated-instances reproof)"
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

def runProofCli (paths : List String) (raw : Bool := false) (strict : Bool := false) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: semanteq [--raw] --proof <fixture.lean|dir> [...]"
    return 1
  let files ← expandPaths paths
  for f in files do
    IO.eprintln s!"[proof-audit] {f}"
    let r ← auditFixture f (strict := strict)
    if raw then IO.println r.toJson.compress else IO.print r.render
    (← IO.getStdout).flush
  return 0

end ProofAudit
end SemantEq
