import SemantEq.Statement
import SemantEq.Config

/-!
# The structure-repackaging arm

For pairs whose preambles declare different but isomorphic structures (the
case the shared-preamble paths cannot share), the bridge is to rebuild each
side's structure values from the other side's fields, apply the antecedent to
the repackaged hypotheses, and rebuild the conclusion. The arm does this at
three grades:

* definitional: a target field closes against any atom of the facts pool,
  which is every hypothesis, every structure field (parents recursed) and
  every conjunct, flattened (`flattenFact`), so renamed fields, regrouped
  conjunctions and split or merged axioms all reduce to pool membership;
* decomposition: a conjunction splits and recurses; a pair-local structure
  applies its constructor and fills each field from the same pool;
* one bridge: a field that survives both gets one audited rewrite proposed by
  the rewrite index against the field type, which statement-level discovery
  never sees since field types live inside structure declarations; the goal
  is rewritten once and the pool retried (depth one by construction).

Data fields follow the same cascade: a same-data field closes by definitional
equality against the source projection, a defaulted field is an ordinary
constructor goal. Genuinely new data is out of scope; such a field fails and
the arm declines. The arm is a no-op unless a pair-local structure constant
occurs in the goal or in the antecedent's statement. Audits are the caller's
job: the proof term flows through the standard chain.
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

/-- Is `n` a pair-local structure constant? -/
def isPairLocalStruct (env : Environment) (n : Name) : Bool :=
  (refNamespace.isPrefixOf n || candNamespace.isPrefixOf n)
    && (getStructureInfo? env n).isSome

/-- Does `e` mention any pair-local structure constant? (cheap arm gate) -/
def mentionsPairLocalStruct (env : Environment) (e : Expr) : Bool :=
  (e.getUsedConstants.filter (isPairLocalStruct env)).size > 0

/-- Flatten a fact into its usable atoms: the fact itself, both components of
a conjunction (recursively), every field of a pair-local structure value
(parents recursed through their subobject projections). The result is the
facts pool: target fields close against any atom, so field names, grouping
and structure nesting on the source side stop mattering. -/
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

/-- Is `ty` headed by a pair-local structure that has a counterpart in the
opposite namespace? Returns the twin's type when so, the only shape for which
opening a binder buys anything (see `fillGoal`'s intro case). -/
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
  -- (1.5) targeted intro: open a binder only when its domain is a pair-local
  -- structure with a counterpart, since twinning needs a term to project from
  -- and such a binder may sit under a conjunct or a constructor field. Tested
  -- on the un-whnf'd type: `¬A` and `a ≠ b` must not become intro targets.
  -- Each intro consumes one structure binder, which bounds the recursion.
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
  -- (4) one bridge lemma from the rewrite index, then retry 1–3: as a
  -- single-lemma `simp only` first (field types are usually quantified, their
  -- redexes under binders where `rw` cannot reach), then as a plain `rw`
  if allowRw then
    -- unfold pair-local definitions in the goal first: a differing local
    -- definition hides the redex the bridge lemma must match
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

/-- The repackaging arm. Builds a proof of `goalType` from `ante` when the gap
between the two sides is pair-local structures (possibly nested, regrouped or
one rewrite apart). Returns the elaborated proof; audits are the caller's
job, the same contract as every other arm. -/
def repackagingClose (ante : Name) (goalType : Expr) (forbid : NameSet := {})
    : MetaM (Option Expr) := do
  let env ← getEnv
  let some anteInfo := env.find? ante | return none
  unless mentionsPairLocalStruct env goalType
      || mentionsPairLocalStruct env anteInfo.type do return none
  let trace := (← getConfig).trace
  if trace then IO.eprintln "[repack] gate passed"
  let s ← saveState
  try
    -- lazy rewrite-index tree: one per arm invocation, queried only by fields
    -- that reach the bridge grade; `forbid` mirrors discovery's set
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
    if (← getConfig).trace then
      IO.eprintln s!"[repack] exception: {← e.toMessageData.toString}"
    restoreState s
    return none
end SemantEq
