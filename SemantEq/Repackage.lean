import SemantEq.RestrictedSearch
import SemantEq.Statement
import SemantEq.Env

/-!
# The structure-repackaging arm

For pairs whose preambles declare DIFFERENT-but-isomorphic structures — the
case the shared-preamble paths rightly refuse to share — the honest bridge is the probe-B
move: rebuild each side's structure values from the other side's fields,
apply the antecedent to the repackaged hypotheses, and rebuild the
conclusion. This module mechanizes that move at three grades :

* **A (defeq)** — a target field closes against ANY atom of the facts pool
  by definitional equality. Fields are NOT matched by name: the pool is
  every hypothesis, every structure field (parents recursed), and every
  ∧-component, flattened (`flattenFact`) — so renamed fields, re-grouped
  conjunctions, and split/merged axioms all reduce to pool membership.
* **∧/structure decomposition** — ∧-headed target fields split and recurse;
  pair-local-structure-headed targets apply their constructor and fill each
  field from the same pool, recursively (`extends`-parents are fields).
* **B (single-lemma bridge)** — a field that survives all of the above gets
  ONE audited rewrite: `Meta.Rewrites.findRewrites` (the rw?-index, lazy
  module tree created at most once per arm invocation) proposes Eq/Iff
  bridges against the FIELD type — which statement-level discovery can never
  see, since field types live inside structure declarations — the goal is
  rewritten once, and the pool is retried. Depth 1 by construction
  (`allowRw := false` in the retry).

Data fields ride the same cascade: same-data fields close by defeq against
the source projection (D1); defaulted fields are ordinary constructor goals
filled the same way (D2). Genuinely new data (D3) is out of scope — such a
field fails and the arm declines, honestly.

Self-containment: the arm no-ops instantly unless a pair-local structure
constant (under `SemantEqRef`/`SemantEqCand`) occurs in the goal or the
antecedent's statement — possible only for declaring-preamble pairs. Audits
are the caller's job, unchanged: the proof term (constructors, projections,
∧-plumbing, Eq/Iff-grade bridge lemmas) flows through the standard stack.
-/

namespace SemantEq

open Lean Meta

/-- Swap a pair-local name to its opposite-namespace counterpart. -/
def crossName? (n : Name) : Option Name :=
  if refNamespace.isPrefixOf n then
    some (n.replacePrefix refNamespace candNamespace)
  else if candNamespace.isPrefixOf n then
    some (n.replacePrefix candNamespace refNamespace)
  else none

/-- Is `n` a pair-local STRUCTURE constant? -/
def isPairLocalStruct (env : Environment) (n : Name) : Bool :=
  (refNamespace.isPrefixOf n || candNamespace.isPrefixOf n)
    && (getStructureInfo? env n).isSome

/-- Does `e` mention any pair-local structure constant? (cheap arm gate) -/
def mentionsPairLocalStruct (env : Environment) (e : Expr) : Bool :=
  (e.getUsedConstants.filter (isPairLocalStruct env)).size > 0

/-- Flatten a fact into its usable atoms: the fact itself; both components
of an ∧ (recursively); every field of a pair-local structure value
(parents recursed via their subobject projections). The result is the
"facts pool" — target fields close against ANY atom, so field names,
grouping, and structure nesting on the source side stop mattering. -/
partial def flattenFact (f : Expr) : MetaM (Array Expr) := do
  let ty ← whnf (← inferType f)
  let mut out := #[f]
  if ty.isAppOfArity ``And 2 then
    if let some l ← observing? (mkAppM ``And.left #[f]) then
      out := out ++ (← flattenFact l)
    if let some r ← observing? (mkAppM ``And.right #[f]) then
      out := out ++ (← flattenFact r)
    return out
  let .const sn _ := ty.getAppFn | return out
  let env ← getEnv
  if isPairLocalStruct env sn then
    if let some si := getStructureInfo? env sn then
      for fname in si.fieldNames do
        if let some proj ← observing? (mkProjection f fname) then
          out := out ++ (← flattenFact proj)
  return out

/-- Is `ty` headed by a pair-local structure that HAS a counterpart in the
opposite namespace? Returns the twin's type when so — the only shape for
which opening a binder buys anything (see `fillGoal`'s intro case). -/
def twinTypeOf? (env : Environment) (ty : Expr) : Option Expr :=
  match ty.getAppFn with
  | .const sn us =>
    if isPairLocalStruct env sn then
      match crossName? sn with
      | some cn =>
        if (getStructureInfo? env cn).isSome then
          some (mkAppN (.const cn us) ty.getAppArgs)
        else none
      | none => none
    else none
  | _ => none

/-- Close goal `g` from the facts pool: (1) any atom by defeq; (2) ∧-split;
(3) pair-local-structure constructor, fields recursively; (4) one rewrite
bridge from the rw?-index (`probe`), then retry 1–3. Every attempt rolls
back on failure. -/
partial def fillGoal (probe : MVarId → MetaM (List Meta.Rewrites.RewriteResult))
    (facts : Array Expr) (g : MVarId) (allowRw : Bool := true) : MetaM Bool := do
  let s ← saveState
  -- (1) direct defeq against any atom
  for f in facts do
    let s' ← saveState
    let hit ← try
        if ← isDefEq (← g.getType) (← inferType f) then
          g.assign f; pure true
        else pure false
      catch _ => pure false
    if hit then return true
    restoreState s'
  -- (1.5) TARGETED intro : open a binder ONLY when
  -- its domain is a pair-local structure with a counterpart — i.e. because it
  -- HIDES twinnable material, never as a general habit. Blanket intro is what
  -- the ladder's two intro depths (`introsToFirstPropHyp` vs full `intros`)
  -- exist to avoid: stripping a goal can destroy the very shape another arm
  -- needs. Here the purpose is specific — twinning needs a TERM to project
  -- from, and a structure binder nested under `∧`/a constructor field is
  -- unreachable from `repackagingClose`'s single root-level `intros`.
  -- Tested on the UN-whnf'd type: `¬A` / `a ≠ b` whnf to `_ → False`, and
  -- those must not become intro targets. Bounded by the number of structure
  -- binders (each intro strictly consumes one), not by fuel.
  let rawTgt ← instantiateMVars (← g.getType)
  if rawTgt.isForall then
    if let some twinTy := twinTypeOf? (← getEnv) rawTgt.bindingDomain! then
      let ok ← try
          let (fv, g') ← g.intro1
          g'.withContext do
            let h := mkFVar fv
            let mut facts' := facts ++ (← flattenFact h)
            -- the whole point: twin the newly-exposed structure hypothesis
            let tw ← mkFreshExprMVar twinTy
            if ← fillGoal probe facts' tw.mvarId! allowRw then
              facts' := facts' ++ (← flattenFact (← instantiateMVars tw))
            fillGoal probe facts' g' allowRw
        catch _ => pure false
      if ok then return true
      restoreState s
  let tgt ← whnf (← g.getType)
  -- (2) ∧-split
  if tgt.isAppOfArity ``And 2 then
    let ok ← try
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
        let mut all := true
        for g' in gs do
          unless ← fillGoal probe facts g' allowRw do all := false; break
        pure all
      catch _ => pure false
    if ok then return true
    restoreState s
  -- (3) pair-local structure: constructor, fill fields from the same pool
  if let .const sn _ := tgt.getAppFn then
    if isPairLocalStruct (← getEnv) sn then
      let ok ← try
          let ctor := getStructureCtor (← getEnv) sn
          let fieldGoals ← g.apply (← mkConstWithFreshMVarLevels ctor.name)
          let mut all := true
          for fg in fieldGoals do
            unless ← fillGoal probe facts fg allowRw do all := false; break
          pure all
        catch _ => pure false
      if ok then return true
      restoreState s
  -- (4) B-level: ONE bridge lemma from the rw?-index, then retry 1–3.
  -- Tried as a single-lemma `simp only` FIRST — field types are typically
  -- ∀-quantified and their redexes sit under binders, where `rw` cannot
  -- reach — with the plain `rw` shape as fallback for non-simp-orientable
  -- rewrites. Depth 1 by construction (`allowRw := false` in the retry).
  if allowRw then
    -- δ-unfold pair-local defs in the goal first (pure defeq replacement):
    -- differing local defs appear as FOLDED constant applications in field
    -- types, hiding the redexes the bridge lemma must match from the
    -- rw?-probe (observed: the diff-natpast pair — `natPast B s` folds the
    -- `⨆` the iSup-family lemma rewrites).
    let g ← try
        let tgt ← g.getType
        let tgtU ← Meta.deltaExpand tgt fun n =>
          refNamespace.isPrefixOf n || candNamespace.isPrefixOf n
        if tgtU != tgt then g.replaceTargetDefEq (← Core.betaReduce tgtU) else pure g
      catch _ => pure g
    let results ← try probe g catch _ => pure []
    for r in results.take 12 do
      if let some lem := r.expr.getAppFn.constName? then
        let s' ← saveState
        let ok ← try
            let st ← ({} : SimpTheorems).addConst lem (inv := r.symm)
            let ctx ← Simp.mkContext {} (simpTheorems := #[st])
              (congrTheorems := ← getSimpCongrTheorems)
            match ← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := #[]) with
            | (none, _) => pure true  -- the lemma alone closed the goal
            | (some (_, g'), _) => fillGoal probe facts g' (allowRw := false)
          catch _ => pure false
        if ok then return true
        restoreState s'
      let s' ← saveState
      let ok ← try
          let rr ← g.rewrite (← g.getType) r.expr r.symm
          let g' ← g.replaceTargetEq rr.eNew rr.eqProof
          fillGoal probe facts g' (allowRw := false)
        catch _ => pure false
      if ok then return true
      restoreState s'
  restoreState s
  return false

/-- The repackaging arm. Builds a proof of `goalType` from `ante` when the
gap between the two sides is (possibly nested, re-grouped, or
single-rewrite-bridged) pair-local structures. Returns the elaborated
proof; audits are the caller's job — same contract as every native arm. -/
def repackagingClose (ante : Name) (goalType : Expr) (forbid : NameSet := {})
    : MetaM (Option Expr) := do
  let env ← getEnv
  let some anteInfo := env.find? ante | return none
  unless mentionsPairLocalStruct env goalType
      || mentionsPairLocalStruct env anteInfo.type do return none
  let trace := (← envVar "TRACE").isSome
  if trace then IO.eprintln "[repack] gate passed"
  let s ← saveState
  try
    -- lazy rw?-module tree: one per arm invocation, queried only by fields
    -- that reach the B-level bridge; forbid mirrors discovery's set
    let tree ← Meta.Rewrites.createModuleTreeRef
    let probe (g : MVarId) : MetaM (List Meta.Rewrites.RewriteResult) := do
      g.withContext do
        Meta.Rewrites.findRewrites #[] tree g (← instantiateMVars (← g.getType))
          (forbidden := forbid) (side := .none)
          (stopAtRfl := false) (max := 12) (leavePercentHeartbeats := 10)
    let root := (← mkFreshExprMVar goalType).mvarId!
    let (_, g) ← root.intros
    g.withContext do
    let hyps ← getLocalHyps
    let mut facts : Array Expr := #[]
    for h in hyps do
      facts := facts ++ (← flattenFact h)
    -- cross-namespace twin of every structure-typed hypothesis
    for h in hyps do
      let hTy ← whnf (← inferType h)
      let some twinTy := twinTypeOf? env hTy | continue
      let tw ← mkFreshExprMVar twinTy
      if ← fillGoal probe facts tw.mvarId! then
        facts := facts ++ (← flattenFact (← instantiateMVars tw))
    if trace then IO.eprintln s!"[repack] facts+twins: {facts.size}"
    -- instantiate the antecedent against the pool
    let anteC ← mkConstWithFreshMVarLevels ante
    let (margs, _, _) ← forallMetaTelescope (← inferType anteC)
    for m in margs do
      let mTy ← instantiateMVars (← inferType m)
      if ← m.mvarId!.isAssigned then continue
      if (← Meta.isProp mTy) then
        for fct in facts do
          unless ← m.mvarId!.isAssigned do
            if ← isDefEq mTy (← inferType fct) then
              m.mvarId!.assign fct
      else if (← isClass? mTy).isSome then
        if let some inst ← observing? (synthInstance mTy) then
          m.mvarId!.assign inst
    let r ← instantiateMVars (mkAppN anteC margs)
    if r.hasExprMVar then
      if trace then IO.eprintln "[repack] ante instantiation incomplete"
      restoreState s
      return none
    facts := facts ++ (← flattenFact r)
    if trace then IO.eprintln s!"[repack] ante applied; total facts {facts.size}; proving"
    let closed ← fillGoal probe facts g
    unless closed do restoreState s; return none
    let proof ← instantiateMVars (mkMVar root)
    restoreState s
    return some proof
  catch e =>
    if (← envVar "TRACE").isSome then
      IO.eprintln s!"[repack] exception: {← e.toMessageData.toString}"
    restoreState s
    return none

end SemantEq
