import Lean
import SemantEq.Config
import SemantEq.Logic
import SemantEq.Audit
import SemantEq.InstancePack

/-!
# The structural closer

Restricted by construction: the antecedent is asserted into the context, its
replumbing variants added, quantified hypotheses forward-instantiated against
the locals, the context saturated (∧/∃/↔/∨ destructured), and `solveByElim`
run over an explicit lemma list. `structuralCore` is the tail every arm ends
in; `structuralClose` is the arm that uses nothing else; `goalDefeqTrue` is
the triviality probe.
-/

namespace SemantEq
open Lean Meta

/-- Lemma set for the structural `solveByElim`. Deliberately narrow: the
antecedent plus extensionality bridges with `Eq`-shaped conclusions.
Projections with a variable conclusion (`And.left`, `Iff.mp`) do not belong
here: their conclusions unify with every goal and backward search over them
explodes. Destructuring is done by hypothesis saturation instead; the
antecedent's iff directions are covered by the restricted search's
`(ante, .mp/.mpr)` candidates. -/
def structuralSolveLemmas (ante : Name) : List Name :=
  [ante, ``Subtype.ext, ``Prod.ext] ++ sideConditionCore

/-- The search's lemma list without the antecedent: what the triviality probe
and the antecedent-free replays are allowed to use. -/
def noAnteLemmas : List Name :=
  [``Subtype.ext, ``Prod.ext] ++ sideConditionCore

/-- Replumbing variants: packaging-only transforms of a proof term, pushed
under its ∀-telescope: `Eq.symm`, `Iff.symm` and `Ne.symm` flips, `Iff.mp`,
`Iff.mpr`, `And.left` and `And.right` projections. `saturateHyps` destructures
only at the top level of a hypothesis; a quantified hypothesis (`∀ x, P x ∧
Q x`, `∀ x, f x = g x`) hides its structure under the binders, the shape of
one-token `.symm` and `.1` proofs. Projections recurse (they strictly reduce
structure); flips do not (`symm ∘ symm` would loop). Everything is built from
the term plus `Eq.symm`/`Iff.mp`-grade plumbing, which the audit grades
schematic or eliminator, so the variants are audit-safe by construction. -/
partial def plumbVariants (e : Expr) (maxOut : Nat := 12) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  let mut queue : Array Expr := #[e]
  while !queue.isEmpty && out.size < maxOut do
    let cur := queue.back!
    queue := queue.pop
    let ty ← inferType cur
    let (flips, projs) ← forallTelescope ty fun xs body => do
      let app := mkAppN cur xs
      let mut flips : Array Expr := #[]
      let mut projs : Array Expr := #[]
      match body.getAppFn.constName?.getD .anonymous with
      | ``Eq =>
        flips := flips.push (← mkAppM ``Eq.symm #[app])
        -- Eq of sets / of functions: expose the pointwise content via the
        -- Iff-conclusioned plumbing bridges (recursion then gives the .mp/.mpr
        -- of the pointwise iff under the new binder)
        let args := body.getAppArgs
        if args.size == 3 then
          let bridge? : Option Name :=
            if args[0]!.getAppFn.constName?.getD .anonymous == `Set then
              some `Set.ext_iff
            else if args[0]!.isForall then
              some `funext_iff
            else none
          if let some bridge := bridge? then
            if (← getEnv).contains bridge then
              try
                projs := projs.push
                  (← mkAppM ``Iff.mp #[← mkConstWithFreshMVarLevels bridge, app])
              catch _ => pure ()
      | ``Ne => flips := flips.push (← mkAppM ``Ne.symm #[app])
      | ``Iff =>
        flips := flips.push (← mkAppM ``Iff.symm #[app])
        projs := projs.push (← mkAppM ``Iff.mp #[app])
        projs := projs.push (← mkAppM ``Iff.mpr #[app])
      | ``And =>
        projs := projs.push (← mkAppM ``And.left #[app])
        projs := projs.push (← mkAppM ``And.right #[app])
      | _ => pure ()
      let flipTerms ← flips.mapM (mkLambdaFVars xs ·)
      let projTerms ← projs.mapM (mkLambdaFVars xs ·)
      return (flipTerms, projTerms)
    out := out ++ flips ++ projs
    queue := queue ++ projs
  return out.shrink maxOut

/-- Assert the replumbing variants of every Prop hypothesis into the goal's
context (capped), so saturation and `solveByElim` see the under-binder
structure. Hypotheses produced here are consequences of existing ones, never
new content. -/
def assertVariants (g : MVarId) (cap : Nat := 24) : MetaM MVarId := do
  -- most recent hypotheses first: the asserted antecedent sits at the end of the
  -- context and must not lose its variant budget to the goal's own hypotheses
  let hyps := (← g.getNondepPropHyps).reverse
  let mut g := g
  let mut n := 0
  for fv in hyps do
    if n ≥ cap then break
    let vs ← try g.withContext (plumbVariants (mkFVar fv)) catch _ => pure #[]
    for v in vs do
      if n < cap then
        try
          let ty ← g.withContext (inferType v)
          g ← g.assert ((`h_plumb).appendIndexAfter n) ty v
          let (_, g') ← g.intro1P
          g := g'
          n := n + 1
        catch _ => pure ()
  return g

/-- Saturate the local context: destructure every hypothesis whose head is
`And`, `Exists`, `Iff` or `Or` (the `obtain`/`rcases` shapes). `Or` branches
multiply the goals; everything else just enriches the context. -/
partial def saturateHyps (g : MVarId) (fuel : Nat := 12) : MetaM (List MVarId) := do
  if fuel == 0 then
    return [g]
  let target? ← g.withContext do
    for h in ← getLCtx do
      unless h.isImplementationDetail do
        let head := (← whnfR h.type).getAppFn.constName?.getD .anonymous
        if head == ``And || head == ``Exists || head == ``Iff || head == ``Or then
          return some h.fvarId
    return none
  match target? with
  | none => return [g]
  | some fvarId =>
    let subs ← g.cases fvarId
    let mut acc := []
    for s in subs do
      acc := acc ++ (← saturateHyps s.mvarId (fuel - 1))
    return acc

/-- Run `solveByElim` restricted to an explicit lemma list (plus the local
hypotheses and the harmless defaults `rfl`, `trivial`, `congrFun`,
`congrArg`). Restricted by construction: no library search happens here.
Returns the remaining goals. -/
def structuralSolve (lemmaNames : List Name) (goals : List MVarId)
    (maxDepth : Nat := 16) (transparency? : Option TransparencyMode := none)
    (constructor : Bool := true) : MetaM (List MVarId) := do
  let cfg : SolveByElim.SolveByElimConfig :=
    { maxDepth, exfalso := false, symm := true, commitIndependentGoals := true,
      transparency := transparency?.getD (← getTransparency), constructor }
  let adds : List Term := lemmaNames.map fun n => mkIdent n
  let ⟨lemmas, ctx⟩ ← SolveByElim.mkAssumptionSet false false adds [] #[]
  SolveByElim.solveByElim cfg lemmas ctx goals

/-- Delayed-instance application of the antecedent. An instance binder of the
antecedent may be met by a local instance only up to unfolding a definition
(`[(H.subgroupOf K).Characteristic]` in the context against the antecedent's
`[(comap K.subtype H).Characteristic]`, where `subgroupOf` is that comap by
definition); `synthInstance` matches at reducible transparency and cannot see
it. `allowSynthFailures := true` turns the failed instance binders into
goals, and the structural finisher, which unifies at default transparency,
closes them from the context along with the Prop arguments. The proof term is
the antecedent applied to context material, so the audits apply unchanged. -/
def applyDelayedInstance (goalType : Expr) (ante : Name) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let (_, g) ← root.mvarId!.intros
    let f ← mkConstWithFreshMVarLevels ante
    let goals ← g.apply f (cfg := { allowSynthFailures := true })
    let rem ← structuralSolve (structuralSolveLemmas ante) goals
    unless rem.isEmpty do
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

/-- Forward instantiation: specialize each ∀-headed Prop hypothesis (most
importantly the asserted antecedent) against the local context, every binder
filled by a local of definitionally equal type (backtracking, bounded) and
instances synthesized, and assert the instantiated body when its head is
destructurable (∃, ∧, ↔, ∨). This is what exposes a hypothesis-side witness:
for `h_ante : ∀ x U …, ∃ V, …` no goal-side `apply` can expose the `∃`, while
after intros the goal's locals mirror the antecedent's binders, so the
specialization is usually forced. Pure modus ponens over existing hypotheses,
no new constants. -/
def forwardInstantiate (g : MVarId) (maxAsserts : Nat := 6) : MetaM MVarId := do
  packMemoRef.modify fun m => { m with built := #[] }   -- fresh collection for this pass
  let hyps := (← g.getNondepPropHyps).reverse
  let mut g := g
  let mut n := 0
  for fv in hyps do
    if n ≥ maxAsserts then break
    let inst? ← g.withContext do
      try
        let ty ← instantiateMVars (← fv.getType)
        unless ty.isForall do return none
        let (ms, infos, body) ← forallMetaTelescope ty
        -- binder cap 16: research-level statements carry around fifteen
        -- binders; the cost is bounded by the filler's budget, not by the cap
        if ms.isEmpty || ms.size > 16 then return none
        unless (← isProp body) do return none
        let head := (← whnfR body).getAppFn.constName?.getD .anonymous
        let destructurable :=
          head == ``Exists || head == ``And || head == ``Iff || head == ``Or
        -- an atomic body may be exactly the goal (pure modus ponens): unify it
        -- against the goal first, so the goal fixes the data arguments before
        -- the filler and the pack moves discharge the rest
        if !destructurable then
          unless ← isDefEq body (← g.getType) do
            return none
        let mut locals : Array Expr := #[]
        for h in ← getLCtx do
          unless h.isImplementationDetail || h.fvarId == fv do
            locals := locals.push (mkFVar h.fvarId)
        let budget ← IO.mkRef (300 : Nat)
        unless (← fillFromLocals budget locals ms infos 0) do return none
        let args ← ms.mapM instantiateMVars
        if args.any (·.hasExprMVar) then return none
        let body ← instantiateMVars body
        if body.hasExprMVar then return none
        return some (body, mkAppN (mkFVar fv) args)
      catch _ => return none
    if let some (ty, val) := inst? then
      try
        g ← g.assert ((`h_fwd).appendIndexAfter n) ty val
        let (_, g') ← g.intro1P
        g := g'
        n := n + 1
      catch _ => pure ()
  -- every instance the pack pass constructed is asserted into the context:
  -- `assert`/`intro1P` go through `withNewLocalInstances`, so each becomes a
  -- real local instance that the structural close and instance synthesis find
  let mut seenTy : List String := []
  let mut k := 0
  for (ty, v) in (← packMemoRef.get).built do
    let key ← try packKey ty catch _ => pure ""
    unless key.isEmpty || seenTy.contains key do
      seenTy := key :: seenTy
      try
        g ← g.assert ((`h_inst).appendIndexAfter k) ty v
        let (_, g') ← g.intro1P
        g := g'
        k := k + 1
      catch _ => pure ()
  return g

/-- Substitute local equations whose side is a free variable (`hf : f = X^3 + …`
⊢ `Irreducible f`, the `rw [hf]` shape): pure `Eq.subst` plumbing, applied
hypothesis-side. One failed substitution stops the pass (the context indices
shift after each success). -/
def substEqHyps (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:8] do
    match ← try substSomeVar? g catch _ => pure none with
    | some g' => g := g'
    | none => break
  return g
mutual

/-- The shared tail of every structural closer, over an explicit lemma list:
substitute variable equations, enrich the context with replumbing variants,
forward-instantiate quantified hypotheses against the locals, saturate
(destructure ∧/∃/↔/∨ hypotheses), then `solveByElim` over the lemmas +
hypotheses per goal. Goals that survive get the apply-hypothesis-and-recurse
round (`applyHypRecurseCore`). Returns the remaining goals. -/
partial def structuralCore (lemmas : List Name) (g : MVarId) (depth : Nat := 1)
    : MetaM (List MVarId) := do
  let g ← substEqHyps g
  -- variants and forward instantiations are asserted into the context and so
  -- persist into the recursive rounds
  let g ← assertVariants g
  let g ← forwardInstantiate g
  let goals ← saturateHyps g (fuel := 24)
  -- per goal: `solveByElim` throws on failure (it never returns partial
  -- leftovers), and one hard sibling must not doom the rest
  let mut out := []
  for gg in goals do
    -- and-split first, so the deep solvers only ever run on atoms; it rolls
    -- back wholesale on failure, leaving the goal untouched for the path below
    let isAnd ← try
        pure ((← whnfR (← gg.getType)).getAppFn.constName?.getD .anonymous == ``And)
      catch _ => pure false
    if isAnd then
      if ← andSplitThenRecurse lemmas gg depth then continue
    let closed ← try
      pure (← structuralSolve lemmas [gg]).isEmpty
    catch _ => pure false
    if closed then continue
    if depth > 0 then
      if ← applyHypRecurseCore lemmas gg depth then continue
    out := out ++ [gg]
  return out

/-- And-only split, passing the same `depth` to the recursive `structuralCore`:
`And.intro` strictly decreases the goal, so nesting terminates on the
conjunction's own structure and must not consume the apply-hypothesis
recursion budget (at `depth := 1` a five-fold conclusion would otherwise
split once and hand the rest to blind search). All-or-nothing rollback. -/
partial def andSplitThenRecurse (lemmas : List Name) (g : MVarId) (depth : Nat)
    : MetaM Bool := do
  unless (← whnfR (← g.getType)).getAppFn.constName?.getD .anonymous == ``And do
    return false
  let trace := (← getConfig).trace
  let st ← saveState
  let ok ← try
    let subs ← g.applyConst ``And.intro
    if trace then
      IO.eprintln s!"[and-split] fired on: {← Meta.ppExpr (← instantiateMVars (← g.getType))}"
    let mut all := true
    let mut idx := 0
    for sub in subs do
      let (_, sub') ← sub.intros
      idx := idx + 1
      let left ← structuralCore lemmas sub' depth
      if trace then
        IO.eprintln s!"[and-split]   subgoal {idx}: {if left.isEmpty then "closed" else "OPEN"}"
        if !left.isEmpty then
          for lg in left.take 1 do
            IO.eprintln s!"[and-split]     residual: {← Meta.ppExpr (← instantiateMVars (← lg.getType))}"
      unless left.isEmpty do
        all := false
        break
    pure all
  catch _ => pure false
  if ok then return true
  restoreState st
  return false

/-- Apply a quantified Prop hypothesis (the asserted antecedent first, since the
context is scanned most recent first) to the goal and recursively finish each
side goal. This is the `refine ante (fun … => ?_) h` shape: the antecedent's
∀-hypothesis argument is itself a replumbing problem (reshuffle the
corresponding local hypothesis under its binders), unreachable by
`solveByElim` alone. -/
partial def applyHypRecurseCore (lemmas : List Name) (g : MVarId) (depth : Nat)
    : MetaM Bool := do
  let hyps := (← g.getNondepPropHyps).reverse
  for fv in hyps.toList.take 6 do
    let s ← saveState
    let ok ← try
      let subs ← g.apply (mkFVar fv)
      let mut all := true
      for sub in subs do
        let (_, sub') ← sub.intros
        unless (← structuralCore lemmas sub' (depth - 1)).isEmpty do
          all := false
          break
      pure all
    catch _ => pure false
    if ok then
      return true
    restoreState s
  return false
end

/-- `structuralCore` keyed by the antecedent (the closers' entry point). -/
def finishStructurally (ante : Name) (g : MVarId) (depth : Nat := 1)
    : MetaM (List MVarId) :=
  structuralCore (structuralSolveLemmas ante) g depth

/-- Try to fully close `goal` with the structural strategy: intro, bring the
antecedent into the context (so saturation and replumbing variants apply to
it; as a mere `solveByElim` lemma it could never be destructured or flipped),
assert the replumbing variants, saturate (the `obtain` shapes), then
`solveByElim` with goal-constructor splitting. Returns the proof. -/
def structuralClose (ante : Name) (goal : MVarId) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root := goal
    let (_, goal) ← goal.intros
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let goal ← goal.assert `h_ante (← inferType anteExpr) anteExpr
    let (_, goal) ← goal.intro1P
    let remaining ← finishStructurally ante goal
    if remaining.isEmpty then
      return some (← instantiateMVars (mkMVar root))
    restoreState s
    return none
  catch _ =>
    restoreState s
    return none

/-- Probe: is the goal definitionally true (`rfl`-closable after intros)? A pure
triviality signal, never a closer: `1 = 1` and `2 = 2` are both rfl-true and
unrelated. -/
def goalDefeqTrue (goalType : Expr) : MetaM Bool := do
  let s ← saveState
  try
    let g := (← mkFreshExprMVar goalType).mvarId!
    let (_, g) ← g.intros
    g.refl
    restoreState s
    return true
  catch _ =>
    restoreState s
    return false
end SemantEq
