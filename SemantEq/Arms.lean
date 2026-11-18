import Lean
import SemantEq.Config
import SemantEq.Logic
import SemantEq.Audit
import SemantEq.Structural

/-!
# The ladder's arms

Normalization with the restricted simp set, the single-bridge arms (`simp only`
at hypotheses and target, `rw … at *`), the bounded multi-step deep search
over harvested states, and the restricted library search (`exact?` with a
filtering candidate finder). Every accepting arm replays its transform without
the antecedent and discards a close the replay still reaches.
-/

namespace SemantEq
open Lean Meta

/-- The restricted normalization simp set: the `push_cast` extension
(Eq/Iff-conclusioned by construction, its attribute handler rejects anything
else; conditional lemmas' side conditions are discharged only from local
hypotheses), the curated plumbing lemmas, and the antecedent itself as a
rewrite rule. -/
def normalizationContext (ante? : Option Name) : MetaM Simp.Context := do
  let mut st ← NormCast.pushCastExt.getTheorems
  let env ← getEnv
  for n in plumbingLemmas do
    if env.contains n then
      try st ← st.addConst n catch _ => pure ()
  if let some ante := ante? then
    try st ← st.addConst ante catch _ => pure ()
  Simp.mkContext {} (simpTheorems := #[st]) (congrTheorems := ← getSimpCongrTheorems)

/-- The `simpa` generalization: bring a fully general instance of the
antecedent into the local context, normalize both it and the target with the
restricted simp set (cast placement, membership unfolding, negation pushing,
so both ends meet in the middle), then close structurally. Covers the
`simpa [bridges] using ante`, negation-pushing and cast-placement shapes. -/
def normalizeThenSolve (goalType : Expr) (ante : Name) (bridges : Array (Name × Bool) := #[])
    : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let (_, g) ← root.mvarId!.intros
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let anteType ← inferType anteExpr
    let g ← g.assert `h_ante anteType anteExpr
    let (anteFVar, g) ← g.intro1P
    let ctx ← normalizationContext (some ante)
    -- normalize every Prop hypothesis (the goal's own hypotheses may carry the
    -- bridge shape, `x ∈ Set.Ioo 0 1` needing `mem_Ioo`), plus the target
    let hyps ← g.getNondepPropHyps
    let (res, _) ← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := hyps.push anteFVar)
    let finished ← do
      match res with
      | none => pure true  -- simp closed the goal
      | some (_, g') => do
        -- when the normalization fired but the structural tail fails, the
        -- normalized goal is the right starting point for the discovered
        -- bridges: a bridge that only matches the normalized shape is
        -- unreachable from the raw goal
        let step ← if bridges.isEmpty then pure (some g') else
          try
            let mut bst : SimpTheorems := {}
            for (lem, symm) in bridges do
              try bst ← bst.addConst lem (inv := symm) catch _ => pure ()
            let bctx ← Simp.mkContext {} (simpTheorems := #[bst])
              (congrTheorems := ← getSimpCongrTheorems)
            match ← simpGoal g' bctx (simplifyTarget := true)
                     (fvarIdsToSimp := ← g'.getNondepPropHyps) with
            | (none, _)         => pure (none : Option MVarId)
            | (some (_, g2), _) => pure (some g2)
          catch _ => pure (some g')
        match step with
        | none    => pure true
        | some gg => pure (← finishStructurally ante gg).isEmpty
    unless finished do
      restoreState s
      return none
    -- antecedent-free replay: the same normalization without the antecedent
    let vacuous ← if (← getConfig).noReplay then pure false else
      withoutModifyingState do
      orFalse <| withHeartbeats 20000 true do
        let root2 ← mkFreshExprMVar goalType
        let (_, g2) ← root2.mvarId!.intros
        let ctx2 ← normalizationContext none
        let (res2, _) ← simpGoal g2 ctx2
          (simplifyTarget := true) (fvarIdsToSimp := ← g2.getNondepPropHyps)
        match res2 with
        | none => pure true
        | some (_, g2') => pure (← structuralCore noAnteLemmas g2').isEmpty
    if vacuous then
      if (← getConfig).trace then
        IO.eprintln "[semanteq]       normalize: rejected as vacuous"
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      if (← getConfig).trace then
        IO.eprintln s!"[semanteq]       normalize: hygiene reject (sorry={proof.hasSorry} mvar={proof.hasExprMVar})"
        let mvars := (proof.collectMVars {}).result
        for m in mvars do
          IO.eprintln s!"[semanteq]         unassigned ?goal : {← ppExpr (← m.getType)}"
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- Intro binders up to (excluding) the first ordinary Prop hypothesis, the
arm-side mirror of the discovery probes' stop rule. Data and instance binders
are opened; the implication structure a transplant-style close needs stays in
the goal. -/
partial def introsToFirstPropHyp (g : MVarId) : MetaM MVarId := do
  match ← g.getType with
  | .forallE _ d _ bi =>
    if (← isProp d) && bi != .instImplicit then return g
    let (_, g') ← g.intro1P
    introsToFirstPropHyp g'
  | _ => return g

/-- Dedup key for a search state: printed target + sorted non-dependent Prop
hypothesis types. Collapses `ℓ` then `←ℓ` cycles and convergent step orders. -/
def ppState (g : MVarId) : MetaM String := do
  g.withContext do
    let tgt := toString (← ppExpr (← g.getType))
    let mut hs : Array String := #[]
    for h in (← g.getNondepPropHyps) do
      hs := hs.push (toString (← ppExpr (← h.getType)))
    return tgt ++ "||" ++ String.intercalate ";" (hs.qsort (· < ·)).toList

/-- A harvest record for the deep search: a single-lemma arm whose transform
fired, captured as a printed state key plus the tag needed to re-execute it.
Strings and names only, since goal states cannot cross elaboration sessions;
the state is rebuilt from the tag later. Recorded before the close attempt
and discarded for free when a close lands. -/
structure HarvestEntry where
  key     : String
  lem     : Name
  symm    : Bool
  viaSimp : Bool
  shallow : Bool

/-- Bridge application (`rw [lem] at h ⊢`, done right): assert the antecedent,
rewrite all Prop hypotheses (the antecedent included) and the target with a
single discovered Eq/Iff lemma through simp (simp rewrites under binders,
where `rw`'s motive fails on quantified hypotheses and goals), then finish
structurally. One attempt per discovered lemma keeps the rewrite auditable
and the search stepwise. -/
def bridgeAtHyps (goalType : Expr) (ante : Name) (lemmas : Array (Name × Bool))
    (shallow : Bool := false)
    (harvest? : Option (IO.Ref (Array HarvestEntry)) := none) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let g ← if shallow then introsToFirstPropHyp root.mvarId!
            else do let (_, gg) ← root.mvarId!.intros; pure gg
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let g ← g.assert `h_ante (← inferType anteExpr) anteExpr
    let (_, g) ← g.intro1P
    -- `addConst` can reject a lemma (non-rewrite shape); it is skipped rather
    -- than failing the whole arm
    let mut st : SimpTheorems := {}
    for (lem, symm) in lemmas do
      try st ← st.addConst lem (inv := symm) catch _ => pure ()
    let ctx ← Simp.mkContext {} (simpTheorems := #[st])
      (congrTheorems := ← getSimpCongrTheorems)
    let hyps ← g.getNondepPropHyps
    -- simp's own default discharger handles the side conditions of
    -- conditional rewrites
    let (res, _) ← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := hyps)
    let finished ← do
      match res with
      | none => pure true  -- a hypothesis simplified to False
      | some (_, g') => do
        -- harvest the fired state before the `simp only [ante]` pass: the
        -- deep search's step function has no antecedent pass
        if let some ref := harvest? then
          if h : lemmas.size = 1 then
            let (lem, symm) := lemmas[0]
            let key ← ppState g'
            ref.modify (·.push { key, lem, symm, viaSimp := true, shallow })
        -- then the antecedent as a rewrite rule on the target, as a second
        -- pass and not over `h_ante` (in one set simp would collapse `h_ante`
        -- to `True`); if it fires nothing, `simpGoal` throws and the goal stays
        let step ← try
          let mut ast : SimpTheorems := {}
          ast ← ast.addConst ante
          let actx ← Simp.mkContext {} (simpTheorems := #[ast])
            (congrTheorems := ← getSimpCongrTheorems)
          match ← simpGoal g' actx (simplifyTarget := true) (fvarIdsToSimp := #[]) with
          | (none, _)         => pure (none : Option MVarId)   -- ante alone closed it
          | (some (_, g2), _) => pure (some g2)
        catch _ => pure (some g')
        match step with
        | none    => pure true
        | some gg => pure (← finishStructurally ante gg).isEmpty
    unless finished do
      restoreState s
      return none
    -- antecedent-free replay: the same bridge without the antecedent must not
    -- close the goal (a bridge can turn `7 ∣ 49` into `49 % 7 = 0 % 7`, a
    -- definitional triviality the transformed antecedent then "closes")
    let vacuous ← if (← getConfig).noReplay then pure false else
      withoutModifyingState do
      try
        let root2 ← mkFreshExprMVar goalType
        -- parity: replay at the same intros depth as the attempt
        let g2 ← if shallow then introsToFirstPropHyp root2.mvarId!
                 else do let (_, gg) ← root2.mvarId!.intros; pure gg
        let hyps2 ← g2.getNondepPropHyps
        let (res2, _) ← simpGoal g2 ctx (simplifyTarget := true) (fvarIdsToSimp := hyps2)
        match res2 with
        | none => pure true
        | some (_, g2') => pure (← structuralCore noAnteLemmas g2').isEmpty
      catch _ => pure false
    if vacuous then
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- `rw [±lem] at *`: one-shot rewrite of the target and every non-dependent
Prop hypothesis (`h_ante` included), then the structural close. The `rw`
counterpart of `bridgeAtHyps`: it applies the permutative rules `simp`
refuses, and cannot cross binders where simp descends, so each covers the
other's refusals. Side goals of a conditional target rewrite are discharged
structurally; a conditional hypothesis rewrite is skipped (`replaceLocalDecl`
would leave its side goals dangling). The same antecedent-free replay as
every arm. -/
def rwStar (goalType : Expr) (ante : Name) (lem : Name) (symm : Bool)
    (shallow : Bool := false)
    (harvest? : Option (IO.Ref (Array HarvestEntry)) := none)
    (proofOverride? : Option Expr := none) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let g0 ← if shallow then introsToFirstPropHyp root.mvarId!
             else do let (_, g) ← root.mvarId!.intros; pure g
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
    let (_, g1) ← g1.intro1P
    -- transport entries rewrite with their fully-instantiated application
    -- (the bare constant would re-face the underdetermined second carrier)
    let lemExpr : MetaM Expr := match proofOverride? with
      | some p => pure p
      | none => mkConstWithFreshMVarLevels lem
    -- the shared transform: rewrite the target (side goals collected), then each
    -- non-dependent Prop hypothesis; succeeds if any site rewrote
    let rewriteStar (gIn : MVarId) : MetaM (Option (MVarId × List MVarId)) := do
      let mut gg := gIn
      let mut side : List MVarId := []
      let mut any := false
      let tgtRes ← try
          let tgt ← gg.getType
          let r ← gg.rewrite tgt (← lemExpr) symm
          pure (some (← gg.replaceTargetEq r.eNew r.eqProof, r.mvarIds))
        catch _ => pure none
      if let some (g', ms) := tgtRes then
        gg := g'; side := side ++ ms; any := true
      for h in (← gg.getNondepPropHyps) do
        let ok ← try
            let hty ← gg.withContext do instantiateMVars (← h.getType)
            let r ← gg.rewrite hty (← lemExpr) symm
            if !r.mvarIds.isEmpty then pure none
            else pure (some (← gg.replaceLocalDecl h r.eNew r.eqProof))
          catch _ => pure none
        match ok with
        | some res => gg := res.mvarId; any := true
        | none => pure ()
      return if any then some (gg, side) else none
    let some (g2, side) ← rewriteStar g1 | (do restoreState s; return none)
    -- a conditional target rewrite (side goals pending) is not harvested: the
    -- deep step function cannot reproduce a state with an open side obligation
    if let some ref := harvest? then
      if side.isEmpty then
        let key ← ppState g2
        ref.modify (·.push { key, lem, symm, viaSimp := false, shallow })
    let remaining ← finishStructurally ante g2
    let remSide ← structuralSolve (structuralSolveLemmas ante) side
    unless (remaining ++ remSide).isEmpty do
      restoreState s
      return none
    let vacuous ← if (← getConfig).noReplay then pure false else
      withoutModifyingState do
      try
        let root2 ← mkFreshExprMVar goalType
        -- parity: the replay opens binders to the same depth as the attempt
        let gr ← if shallow then introsToFirstPropHyp root2.mvarId!
                 else do let (_, g) ← root2.mvarId!.intros; pure g
        match ← rewriteStar gr with
        | none => pure false
        | some (gg, side2) =>
          let rem2 ← structuralCore noAnteLemmas gg
          let remSide2 ← structuralSolve noAnteLemmas side2
          pure (rem2 ++ remSide2).isEmpty
      catch _ => pure false
    if vacuous then
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- One sequence step of the deep search: a single lemma applied by one
strategy over hypotheses and target. Returns the residual goal, or `none` when
the step did not fire (simp unchanged, rw matched nowhere) or closed the goal
outright (single-step closes are the single-bridge arms' business, already
tried). Conditional rewrites are not allowed in steps. -/
def simpStepOnce (g : MVarId) (lem : Name) (symm : Bool) : MetaM (Option MVarId) := do
  try
    let mut st : SimpTheorems := {}
    st ← st.addConst lem (inv := symm)
    let ctx ← Simp.mkContext {} (simpTheorems := #[st])
      (congrTheorems := ← getSimpCongrTheorems)
    let hyps ← g.getNondepPropHyps
    match (← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := hyps)).1 with
    | none => return none
    | some (_, g') => return some g'
  catch _ => return none

/-- The `rw` strategy of `simpStepOnce`: one-shot rewrite of the target and
each non-dependent Prop hypothesis; at least one site must fire. -/
def rwStepOnce (g : MVarId) (lem : Name) (symm : Bool) : MetaM (Option MVarId) := do
  try
    let mut gg := g
    let mut any := false
    let t ← try
        let tgt ← gg.getType
        let r ← gg.rewrite tgt (← mkConstWithFreshMVarLevels lem) symm
        if r.mvarIds.isEmpty then pure (some (← gg.replaceTargetEq r.eNew r.eqProof))
        else pure none
      catch _ => pure none
    if let some g' := t then
      gg := g'; any := true
    for h in (← gg.getNondepPropHyps) do
      let o ← try
          let hty ← gg.withContext do instantiateMVars (← h.getType)
          let r ← gg.rewrite hty (← mkConstWithFreshMVarLevels lem) symm
          if r.mvarIds.isEmpty then pure (some (← gg.replaceLocalDecl h r.eNew r.eqProof))
          else pure none
        catch _ => pure none
      if let some res := o then
        gg := res.mvarId; any := true
    return if any then some gg else none
  catch _ => return none

/-- Runtime-safe single step: `catch` does not intercept runtime exceptions
(deterministic timeouts, `maxRecDepth`, simp's nested errors), only
`tryCatchRuntimeEx` does, and inside a search over many candidate steps one
exploding candidate must cost that step, not the whole arm. -/
def stepSafe (viaSimp : Bool) (g : MVarId) (lem : Name) (symm : Bool)
    : MetaM (Option MVarId) :=
  tryCatchRuntimeEx
    (if viaSimp then simpStepOnce g lem symm else rwStepOnce g lem symm)
    (fun _ => return none)

/-- Run one path of the deep search: fresh root, staged intros, assert the
antecedent, apply the steps in order, close structurally. The replay runs the
entire sequence without the antecedent at the same intros depth. -/
def runDeepPath (goalType : Expr) (ante : Name)
    (path : List (Name × Bool × Bool)) (shallow : Bool) : MetaM (Option Expr) := do
  let s ← saveState
  let r ← tryCatchRuntimeEx (do
      let root ← mkFreshExprMVar goalType
      let g0 ← if shallow then introsToFirstPropHyp root.mvarId!
               else do let (_, g) ← root.mvarId!.intros; pure g
      let anteExpr ← mkConstWithFreshMVarLevels ante
      let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
      let (_, g1) ← g1.intro1P
      let mut gg := g1
      let mut ok := true
      for (lem, symm, viaSimp) in path do
        match ← stepSafe viaSimp gg lem symm with
        | some g' => gg := g'
        | none => ok := false; break
      if !ok then pure none
      else do
      -- after the sequence, the antecedent as a rewrite rule on the target,
      -- the same optional second pass as the single-bridge arms; the replay
      -- below omits it since it depends on the antecedent
      let afterAnte ← (do
        try
          let mut ast : SimpTheorems := {}
          ast ← ast.addConst ante
          let actx ← Simp.mkContext {} (simpTheorems := #[ast])
            (congrTheorems := ← getSimpCongrTheorems)
          match ← simpGoal gg actx (simplifyTarget := true) (fvarIdsToSimp := #[]) with
          | (none, _)         => pure (none : Option MVarId)   -- ante pass closed it
          | (some (_, g2), _) => pure (some g2)
        catch _ => pure (some gg))
      let closedByStructural ← match afterAnte with
        | none => pure true
        | some gg2 => pure (← finishStructurally ante gg2).isEmpty
      if !closedByStructural then do
        if (← getConfig).trace then
          let show1 := fun (t : Name × Bool × Bool) =>
            let (l, sy, v) := t
            (if v then "simp " else "rw ") ++ (if sy then "← " else "") ++ toString l
          IO.eprintln s!"[deep]   fired-but-unclosed: {path.map show1}"
        pure none
      else do
        let vac ← if (← getConfig).noReplay then pure false else
          tryCatchRuntimeEx (withoutModifyingState do
            let r2 ← mkFreshExprMVar goalType
            let g2init ← if shallow then introsToFirstPropHyp r2.mvarId!
                         else do let (_, g) ← r2.mvarId!.intros; pure g
            let mut g2 := g2init
            let mut ok2 := true
            for (lem, symm, viaSimp) in path do
              match ← stepSafe viaSimp g2 lem symm with
              | some g' => g2 := g'
              | none => ok2 := false; break
            if !ok2 then pure false
            else pure (← structuralCore noAnteLemmas g2).isEmpty)
            (fun _ => pure false)
        if vac then pure none
        else do
          let proof ← instantiateMVars root
          if proof.hasSorry || proof.hasExprMVar then pure none
          else pure (some proof))
    (fun _ => pure none)
  if r.isNone then restoreState s
  return r

/-- The deep search. The single-lemma arms harvest their fired states
(`HarvestEntry`) as they run; if one of them closes, the direction ends and
the harvest is discarded, so this runs only after the whole ladder failed.
The frontier starts as the first `nStateCap` distinct harvested states in arm
order. Per level, under an absolute budget of `levelBudget` heartbeats: every
frontier state is rebuilt from its path (goal states cannot cross elaboration
sessions), the top `nLemmaCap` candidates are applied with both strategies,
every transform landing on a state never seen before (global dedup, which
kills `ℓ`/`←ℓ` cycles) gets the `simp only [ante]` pass and the structural
close at once, and the survivors fill the next frontier up to `nStateCap`.
Running out of budget mid-level keeps the results committed so far and ends
the level. Returns the closing proof and the depth used (the path length),
reported as `bridgeDepth`. -/
def deepSearchLoop (goalType : Expr) (ante : Name)
    (harvest : Array HarvestEntry) (step2Entries : Array (Name × Bool))
    (nLemmaCap nStateCap levelBudget maxDepth : Nat)
    : MetaM (Option (Expr × Nat)) := do
  let trace := (← getConfig).trace
  -- rebuild a frontier state from its path; `none` if a step fails to fire
  let rebuild (path : List (Name × Bool × Bool)) (shallow : Bool)
      : MetaM (Option MVarId) := do
    tryCatchRuntimeEx (do
        let root ← mkFreshExprMVar goalType
        let g0 ← if shallow then introsToFirstPropHyp root.mvarId!
                 else do let (_, g) ← root.mvarId!.intros; pure g
        let anteExpr ← mkConstWithFreshMVarLevels ante
        let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
        let (_, g1) ← g1.intro1P
        let mut gg := g1
        let mut ok := true
        for (lem, symm, viaSimp) in path do
          match ← stepSafe viaSimp gg lem symm with
          | some g' => gg := g'
          | none => ok := false; break
        pure (if ok then some gg else none))
      (fun _ => pure none)
  -- global seen: the two base states + every harvested key
  let seenRef ← IO.mkRef (#[] : Array String)
  for sh in [true, false] do
    let k? ← tryCatchRuntimeEx (withoutModifyingState do
        let root ← mkFreshExprMVar goalType
        let g0 ← if sh then introsToFirstPropHyp root.mvarId!
                 else do let (_, g) ← root.mvarId!.intros; pure g
        let anteExpr ← mkConstWithFreshMVarLevels ante
        let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
        let (_, g1) ← g1.intro1P
        some <$> ppState g1)
      (fun _ => pure none)
    if let some k := k? then seenRef.modify (·.push k)
  -- frontier from the harvest: first come first served in arm order, dedup, cap
  let mut frontier : Array (List (Name × Bool × Bool) × Bool) := #[]
  for h in harvest do
    if frontier.size ≥ nStateCap then break
    unless (← seenRef.get).contains h.key do
      seenRef.modify (·.push h.key)
      frontier := frontier.push ([(h.lem, h.symm, h.viaSimp)], h.shallow)
  if trace then
    IO.eprintln s!"[deep] harvest {harvest.size} fired arms → frontier       {frontier.size} (cap {nStateCap})"
  let winnerRef ← IO.mkRef (none : Option (Expr × Nat))
  let mut level := 2
  while level ≤ maxDepth && !frontier.isEmpty do
    let nextRef ← IO.mkRef (#[] : Array (List (Name × Bool × Bool) × Bool))
    let frontierNow := frontier
    -- side-channel refs carry results out of the budget scope: running out of
    -- heartbeats mid-level keeps everything committed so far
    let _ ← tryCatchRuntimeEx (withHeartbeats levelBudget false do
        for (path, shallow) in frontierNow do
          if (← winnerRef.get).isSome then break
          let some st ← rebuild path shallow | continue
          let last := path.getLast!
          for (l2, s2) in step2Entries.toList.take nLemmaCap do
            if (← winnerRef.get).isSome then break
            unless l2 == last.1 && s2 != last.2.1 do
              for v2 in [true, false] do
                if (← winnerRef.get).isSome then break
                let key? ← tryCatchRuntimeEx (withoutModifyingState do
                    match ← stepSafe v2 st l2 s2 with
                    | some g' => some <$> ppState g'
                    | none => pure none)
                  (fun _ => pure none)
                if let some key := key? then
                  unless (← seenRef.get).contains key do
                    seenRef.modify (·.push key)
                    let newPath := path ++ [(l2, s2, v2)]
                    -- a close attempt on every unseen state
                    match ← runDeepPath goalType ante newPath shallow with
                    | some prf => winnerRef.set (some (prf, newPath.length))
                    | none =>
                      if (← nextRef.get).size < nStateCap then
                        nextRef.modify (·.push (newPath, shallow))
        pure true)
      (fun _ => pure true)
    if let some w ← winnerRef.get then
      if trace then
        IO.eprintln s!"[deep] closed at depth {w.2}"
      return some w
    frontier ← nextRef.get
    if trace then
      IO.eprintln s!"[deep] level {level} done, next frontier {frontier.size}"
    level := level + 1
  return none
open LibrarySearch in
/-- The restricted candidate finder: the default discrimination-tree matches,
filtered during the search and before any application to the antecedent,
structural constants and Eq/Iff-conclusioned lemmas. The antecedent (an
environment-local constant the imported-modules tree does not index) is
prepended explicitly, so "apply the antecedent and discharge its arguments
structurally" is always the first candidate tried. -/
def restrictedFinder (ante : Name) (ty : Expr) : MetaM (Array (Name × DeclMod)) := do
  let cands ← libSearchFindDecls ty
  let cands ← cands.filterM fun (n, _) => do
    if n == ante || structuralWhitelist.contains n || plumbingLemmas.contains n then
      return true
    eqIffConclusioned n
  let anteFirst : Array (Name × DeclMod) := #[(ante, .none), (ante, .mp), (ante, .mpr)]
  return anteFirst ++ cands
open LibrarySearch in
/-- Restricted library search (the search's `exact?`): `librarySearch'`
recomposed with the restricted finder. Candidates stream out, each is audited
as it closes, and the first that passes is accepted, so a plausible but
unauditable first candidate does not discard the direction. Only fully closed
candidates count. Returns the proof and its description. -/
def restrictedSearch (goalType : Expr) (ante : Name)
    (leavePercentHeartbeats : Nat := 10) : MetaM (Option (Expr × String)) := do
  let s ← saveState
  try
    let root := (← mkFreshExprMVar goalType).mvarId!
    let (_, goal) ← root.intros
    let cfg : ApplyConfig := { allowSynthFailures := true }
    if (← getConfig).trace then
      let ctx ← readThe Core.Context
      let now ← IO.getNumHeartbeats
      IO.eprintln s!"[exact?] scope: init={ctx.initHeartbeats} max={ctx.maxHeartbeats} now={now} spent={now - ctx.initHeartbeats}"
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    -- `goal.withContext` is required: after `root.intros` the binders live in
    -- the goal's context, and candidate collection inspects the goal type
    let candidates ← goal.withContext <| librarySearchSymm (restrictedFinder ante) goal
    if (← getConfig).trace then
      IO.eprintln s!"[exact?] candidates collected: {candidates.size}"
    -- per candidate: apply, fill the side goals with the cheap solver `exact?`
    -- itself uses (local assumptions, depth 6, no ex falso), and on a full
    -- close audit at once; the first candidate that passes is accepted, and
    -- an unauditable close continues the scan
    for c in candidates do
      if ← shouldAbort then break
      let rem? ← tryCatch (do
          let ((goal, mctx), (name, mod)) := c
          setMCtx mctx
          let lem ← mkLibrarySearchLemma name mod
          let newGoals ← goal.apply lem cfg
          let rem ← try
              LibrarySearch.solveByElim [] (exfalso := false) newGoals (maxDepth := 6)
            catch _ => pure newGoals
          pure (some rem))
        (fun _ => pure none)
      match rem? with
      | some [] =>
        let proof ← instantiateMVars (mkMVar root)
        -- the explosion check runs here too: the ex-falso ban is polarity-aware
        if (← auditProof ante proof).isNone
            && (← exFalsoVacuous? ante proof).isNone then
          restoreState s
          return some (proof, "restricted exact?")
        restoreState s
      | some _ => restoreState s
      | none => restoreState s
    restoreState s
    return none
  catch e =>
    if (← getConfig).trace then
      IO.eprintln s!"[exact?] swallowed exception: {← e.toMessageData.toString}"
    restoreState s
    return none
end SemantEq
