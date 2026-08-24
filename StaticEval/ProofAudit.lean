import StaticEval.Compile
import StaticEval.Statement
import StaticEval.Search

/-!
# Faithful proof checker (prototype, Plan A applied) — `static_eval --proof <fixture>`

Audits a MODEL-WRITTEN (or hand-written) implication proof for faithfulness, per
`docs/CHECKER_BLUEPRINT.md` v2 + the Plan A fixes (2026-08-06):

* #1 eliminator dispatch precedes the bridge arm (Prop-motive eliminators no
  longer demote case splits to SIDE),
* #2 eliminators keyed semantically (recursor kind / motive-headed conclusion),
  `schematicType` closed over core-logic namespaces,
* #3 sorried in-file theorems = OUTSIDE lemmas with licensed sorry (statement
  graded × role; strict parity — they never rescue a part from "closes ante-free"),
* #4 proven in-file lemmas get the have-Prop asymmetry: ante-free → statement
  graded, proof closed; ante-involved → sanctioned statement, proof expanded,
* #5 goal-shaped local bridges are ledger-flagged.

Verdict per fixture: PASS(flags) / FAIL(reasons) / SKIP_SORRY / ERROR, as JSONL.
-/

namespace StaticEval
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
(REUSE(refactor): supersedes `RestrictedSearch.structuralWhitelist`). -/
def coreLogic : NameSet := .ofList
  [``Eq, ``HEq, ``Iff, ``And, ``Or, ``Not, ``Ne, ``Exists, ``True, ``False]

/-- Plan A #2: the namespace closure — `Exists.intro`, `Or.inl`, `And.casesOn`, …
belong to core logic by their root, so eliminator/constructor mentions inside a
core-logic constant's own type do not break schematicity. -/
def coreLogicName (c : Name) : Bool :=
  coreLogic.contains c || coreLogic.contains c.getRoot

/-- The one retained name list: eliminators of `False`
(REUSE(refactor): mirrors `RestrictedSearch.exFalsoConstants`). -/
def exFalso5 : NameSet := .ofList
  [``False.elim, ``False.rec, ``False.casesOn, ``absurd, ``Not.elim]

/-- Conclusion heads accepted as bridge-grade
(REUSE(refactor): mirrors `RestrictedSearch.acceptedHeads`). -/
def acceptedHeads : List Name := [``Eq, ``Iff, ``HEq, ``Ne]

/-- Is this TYPE a pure logical schema? Allowed: sorts, bound/free variables,
Pi/lambda, and applications headed by a variable or a core-logic constant
(namespace-closed, Plan A #2). -/
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
  /-- Plan A #3: OTHER sorried in-file theorems — outside lemmas with a licensed
  sorry. Never sanctioned, never expanded, never rescue a part from ablation. -/
  assumed    : NameSet := {}
  catMemo    : IO.Ref (NameMap Cat)
  reachMemo  : IO.Ref (NameMap Bool)      -- env-local const → reaches ante?
  sorryMemo  : IO.Ref (NameMap Bool)      -- env-local const → reaches sorryAx?
  localGrade : IO.Ref (NameMap Bool)      -- assumed/ante-free-local: bridge-graded?
  goalParts  : IO.Ref (Array Expr)        -- Plan A #5: ∧-split goal conclusion
  occRoles   : IO.Ref (FVarIdMap Role)
  anteFVars  : IO.Ref FVarIdSet
  fails      : IO.Ref (Array String)
  flags      : IO.Ref (Array String)
  sorryHit   : IO.Ref Bool
  expanded   : IO.Ref NameSet             -- env-local consts already judged-through

def Ctx.fail (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.fails.modify (·.push r)

def Ctx.flag (ctx : Ctx) (r : String) : MetaM Unit :=
  ctx.flags.modify (·.push r)

/-- Constant value with kernel-env fallback; 4.30 hides theorem values behind
`allowOpaque` (REUSE(refactor): discipline of `RestrictedSearch.auditProof`). -/
def valueOf? (env : Environment) (c : Name) : Option Expr := do
  let info ← env.toKernelEnv.find? c <|> env.find? c
  info.value? (allowOpaque := true)

def isLocal (env : Environment) (c : Name) : Bool :=
  (env.getModuleIdxFor? c).isNone

/-- Does env-local constant `c` reach `target` through env-local values? Never
looks inside the ante or the assumed set (their sorries are licensed; they also
must not launder reachability). (REUSE(refactor): mirrors `Search.usesConstant`.) -/
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
  -- plain head FIRST (P2-0 pattern: `Ne` unfolds to `→ False` under a reducing
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
        -- abbrev-wrapped class conclusions (same FP as auditProof, 2026-08-16)
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

/-- Plan A #2: a genuine eliminator — a real recursor, or an elim-suffix-named
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
    -- Plan A #2: eliminators are never bridge — their motive-headed conclusions
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
        -- plain head first, then reducing (REUSE(refactor): P2-0 pattern in
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

/-- `STATIC_EVAL_AUDIT_TRACE`: log every constant grading decision. -/
def auditTrace : IO Bool := do
  return (← IO.getEnv "STATIC_EVAL_AUDIT_TRACE").isSome
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

/-- Plan A #5: do the Iff/Eq sides of this statement unify with a goal part?
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

/-- Plan A #3/#4: an ante-free in-file lemma or a sorried assumption is an
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
(REUSE(refactor): expansion discipline of `RestrictedSearch.auditProof`.) -/
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
(REUSE(refactor): node test of `RestrictedSearch.constructsFalse?`.) -/
def checkFalseNode (ctx : Ctx) (neg : Nat) (e : Expr) (locus : String) : MetaM Unit := do
  if neg > 0 then return ()
  if let some ty ← inferTypeSafe e then
    if ty.isConstOf ``False then
      ctx.fail s!"constructs False in positive position ({locus})"

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

/-- Role-transition heads (Henry, 2026-08-07): `.mp`/`.mpr` conversions of the
two bridge structures. Categorical: the transition projections of Iff and Eq. -/
def transitionHead (c : Name) : Bool :=
  c == ``Iff.mp || c == ``Iff.mpr || c == ``Eq.mp || c == ``Eq.mpr

/-- Simp's goal-conversion wrappers: their argument is a manufactured equation
RECORD (ancillary as a whole), like a transition's record. -/
def recordHead (c : Name) : Bool :=
  c == ``of_eq_true || c == ``of_eq_false

/-- Refinement clause B (2026-08-07): the head is a projection function
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
    (bindersAnte : Bool) (acc : IO.Ref (Array FVarId)) : Expr → MetaM Unit
  | .lam n t b bi => do
    withLocalDecl n bi t fun x => do
      acc.modify (·.push x.fvarId!)
      if bindersAnte then ctx.anteFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body)
      walkLamCollect ctx role neg' bindersAnte acc body
  | e => walk ctx role neg e

partial def walk (ctx : Ctx) (role : Role) (neg : Nat) (e : Expr) : MetaM Unit := do
  match e with
  | .bvar _ | .mvar _ | .sort _ | .lit _ => pure ()
  | .fvar id =>
    recordOcc ctx id role
    checkFalseNode ctx neg e "hypothesis of type False"
  | .const c _ =>
    if c == ctx.ante then pure ()
    else if ctx.assumed.contains c then judgeOutsideLocal ctx role c
    else if isLocal ctx.env c then
      if c.isInternalDetail || (← constReaches ctx ctx.reachMemo ctx.ante c) then
        expandLocal ctx role neg c
      else judgeOutsideLocal ctx role c
    else judgeConst ctx role neg c "bare constant"
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
        -- head judging, by family (#3/#4)
        let isAss := ctx.assumed.contains c
        let isLoc := !isAss && c != ctx.ante && isLocal ctx.env c
        let locInternal := isLoc && c.isInternalDetail
        let locInvolved ← if isLoc && !locInternal then
            constReaches ctx ctx.reachMemo ctx.ante c
          else pure false
        let isLocFree := isLoc && !locInternal && !locInvolved
        if c == ctx.ante then pure ()
        else if isAss || isLocFree then judgeOutsideLocal ctx role c
        else if isLoc then expandLocal ctx role neg c
        else judgeConst ctx role neg c "application head"
        -- argument dispatch
        if c == ctx.ante || locInvolved then
          -- the ante, or an ante-involved local lemma: its arguments feed the
          -- ante pipeline
          for a in args do walk ctx .anteArg neg a
        else if transitionHead c then
          -- Henry's role-transition rule (2026-08-07): a transition transports
          -- the ROLE with the content — the converted proof (last arg) inherits
          -- the conversion's position; the RECORD (the equation/iff being used,
          -- second-to-last arg) is ancillary AS A WHOLE and walks at SIDE.
          for i in [0:args.size] do
            let r := if args.size ≥ 2 && i == args.size - 2 then Role.side else role
            walk ctx r neg args[i]!
        else if recordHead c then
          for i in [0:args.size] do
            let r := if i == args.size - 1 then Role.side else role
            walk ctx r neg args[i]!
        else if let some majorIdx ← projConsumerAnte ctx c args then
          -- refinement clause B: `And.right hod' u …` — args after the
          -- ante-involved record argument feed an ante-derived fact
          for i in [0:args.size] do
            walk ctx (if i > majorIdx then .anteArg else role) neg args[i]!
        else if ← isEliminatorConst ctx.env c then
          -- Plan A #1: eliminator arm BEFORE the bridge arm
          let mut majorInv := false
          for a in args do
            if !a.isLambda then
              if (← isProofSafe a) && (← anteInvolved ctx a) then majorInv := true
          -- refinement clause A: walk minors FIRST, collecting product binders;
          -- a destructured local's occurrence then takes its products' role join
          let products ← IO.mkRef (#[] : Array FVarId)
          for a in args do
            if a.isLambda then
              if ← isProofSafe a then
                -- a genuine minor: its binders are the destructuring products
                walkLamCollect ctx role neg majorInv products a
                if role == .goal && !majorInv then
                  branchAblation ctx a s!"branch of {c}"
              else
                -- motive / predicate lambda: type-level, no products to collect
                walkLam ctx role neg majorInv a
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
        else if ← headIsBridge ctx c (isAss || isLocFree) then
          -- rule (a) RESCOPED (2026-08-07): a bridge applied FORWARD is
          -- role-transparent — its hypotheses are constitutive inputs
          -- (`le_antisymm h1 h2`: the h's ARE the content), not side conditions.
          -- Ancillary protection now lives at the RECORD sites (transitions /
          -- rewrite machinery), where whole equation-manufacture walks at SIDE.
          for a in args do walk ctx role neg a
        else
          let dataHead ← if isAss || isLoc then pure false
            else pure ((← categorize ctx c) == .data)
          for a in args do
            walk ctx role neg a
            if role == .goal && a.isLambda && !dataHead then
              branchAblation ctx a "lambda argument"
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
    : MetaM Unit := do
  let vInv ← anteInvolved ctx b.value
  let propT ← try Meta.isProp b.binderType catch _ => pure false
  withLocalDecl b.binderName b.binderInfo b.binderType fun x => do
    if vInv then ctx.anteFVars.modify (·.insert x.fvarId!)
    let body := b.mkBody x
    let neg' := neg + (← negBump body)
    walk ctx role neg' body
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
        -- Plan A #5: local bridge admitted — flag if it quotes the goal
        if ← goalShaped ctx b.binderType then
          ctx.flag s!"goal-shaped local bridge (have {b.binderName})"
      else
        match jr with
        | some .goal =>
          ctx.fail s!"bare-Prop local hypothesis {b.binderName} used on goal spine"
        | some .anteArg =>
          ctx.flag s!"bare-Prop local hypothesis {b.binderName} feeding ante application"
        | some .side | none => pure ()
    else
      walk ctx (jr.getD role) neg b.value

end

/-- Split a goal conclusion into its ∧-parts (Plan A #5 support). -/
partial def splitAnd (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``And 2 then
    splitAnd (e.getArg! 1) (splitAnd (e.getArg! 0) acc)
  else acc.push e

def computeGoalParts (goalType : Expr) : MetaM (Array Expr) := do
  try
    let (_, _, concl) ← forallMetaTelescope goalType
    return splitAnd concl
  catch _ => return #[]

/-- Confiscated-instances reproof (Henry, 2026-08-07 — the static form of the
adversarial slot for the instance-middleman class): on an otherwise-PASSing
direction, rebuild the goal's telescope, re-assert every ANTE-FREE local binding
the proof itself constructed (data bindings as INSTANCES — the confiscation:
the adversary's packaging is turned against it), and ask a weak prover to close
the conclusion without the ante. Success convicts: the ante was a middleman.
Ante-involved bindings are never confiscated (witness extraction must not leak
ante content into the "ante-free" probe); collection stops at the first one. -/
partial def confiscatedReproof (ctx : Ctx) (goalName : Name)
    (goalType proofVal : Expr) : Term.TermElabM Bool := do
  try
    forallTelescope goalType fun xs concl => do
      let mut body := proofVal
      for x in xs do
        match body with
        | .lam _ _ b _ => body := b.instantiate1 x
        | .mdata _ (.lam _ _ b _) => body := b.instantiate1 x
        | _ => break
      collect concl body
  catch _ => return false
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

/-- Theorem names in source order (top-level `theorem`/`lemma` declarations). -/
def declaredThmNames (src : String) : Array Name := Id.run do
  let mut out := #[]
  for line in src.splitOn "\n" do
    let l := line.trimLeft
    for kw in ["theorem ", "lemma "] do
      if l.startsWith kw then
        let rest := (l.drop kw.length).trimLeft
        let ident := rest.takeWhile fun ch =>
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
  -- Plan A #3: goal = LAST non-sorried theorem; ante = last sorried theorem
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
  let ctx : Ctx := {
    env, ante, assumed
    catMemo := ← IO.mkRef {}, reachMemo := ← IO.mkRef {}, sorryMemo := ← IO.mkRef {}
    localGrade := ← IO.mkRef {}, goalParts := ← IO.mkRef #[]
    occRoles := ← IO.mkRef {}, anteFVars := ← IO.mkRef {}
    fails := ← IO.mkRef #[], flags := ← IO.mkRef #[]
    sorryHit := ← IO.mkRef false, expanded := ← IO.mkRef {} }
  let opts : Options := (maxHeartbeats.set {} 4000000)
  try
    runMetaM env opts do
      ctx.goalParts.set (← computeGoalParts goalType)
      if ← reachesSorry ctx goalVal then
        ctx.sorryHit.set true    -- WIP fixture: the goal proof itself is sorried
      else do
        if !(← anteInvolved ctx goalVal) then
          ctx.fail "proof never touches the antecedent"
        walk ctx .goal 0 goalVal
  catch e =>
    return { file := path, verdict := "ERROR",
             reasons := #[s!"audit crashed: {toString e}"], ante, goal,
             assumed := assumedArr }
  if ← ctx.sorryHit.get then
    return { file := path, verdict := "SKIP_SORRY", ante, goal, assumed := assumedArr }
  let mut fails ← ctx.fails.get
  let flags ← ctx.flags.get
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
    let convicted ← try
        runTermElabM reproofEnv opts (confiscatedReproof ctx goal goalType goalVal)
      catch _ => pure false
    if convicted then
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

def runProofCli (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: static_eval --proof <fixture.lean|dir> [...]"
    return 1
  let files ← expandPaths paths
  for f in files do
    IO.eprintln s!"[proof-audit] {f}"
    let r ← auditFixture f
    IO.println r.toJson.compress
  return 0

end ProofAudit
end StaticEval
