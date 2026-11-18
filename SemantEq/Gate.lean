import Lean
import SemantEq.Config
import SemantEq.Logic
import SemantEq.Structural
import SemantEq.Arms

/-!
# The essential-use gate

The relevance audit: every part of the goal must need the antecedent. The goal
is decomposed into obligations (conjuncts, biconditional sides, ∃-bodies,
hypothesis decorations), each obligation is first rescued against what the
antecedent itself states, and the rest are probed for antecedent-free
provability with the ladder's own machinery minus the antecedent (probe
parity). Runs before the ladder, once per direction.
-/

namespace SemantEq
open Lean Meta Elab

/-- One obligation of the relevance audit. `expr` is closed: generalized over
every binder in scope at its extraction site, ∃-binders included, so a part
`Q x` inside `∃ x, P x ∧ Q x` becomes the obligation `∀ x, Q x` (if that is
provable without the antecedent, the part adds no relational content for any
witness). `decoration` marks Prop binder domains (the `q` of a `q → p`
wrapper, at any depth) as opposed to asserted ∧/↔/∃ parts; the two kinds
rescue against different antecedent pools. -/
structure GateObl where
  expr : Expr
  decoration : Bool
  deriving Inhabited

/-- Recursive obligation decomposer. Walks the goal through `∧` and `↔` (both
sides), `∃` (the body decomposed under the binder, parts re-generalized, so
x-free parts lift out and x-dependent parts become `∀ x, part`), and `∀`/`→`
(a Prop domain is a decoration obligation at any depth, and the body is
decomposed under the binder, so hypothesis binders are kept in part
obligations: the part `3 ∣ n` of `∀ n, 6 ∣ n → … ∧ 3 ∣ n` is the obligation
`∀ n, 6 ∣ n → 3 ∣ n`). When a side of `∧`/`↔` itself split, the side is also
emitted as a whole obligation, since a nested `Even n ↔ n % 2 = 0` is
library-provable as a unit while neither side is. Returns the obligations and
whether anything split; an atom that never split is returned as a single part
so enclosing conjunctions can claim it, and the top-level caller discards
non-decoration parts when nothing split (the whole-goal case belongs to the
triviality probe, not this gate). -/
partial def decomposeObls (xs : Array Expr) (e : Expr) (fuel : Nat)
    (directional : Bool := false) : MetaM (Array GateObl × Bool) := do
  let e ← instantiateMVars e
  let closed (t : Expr) (deco : Bool) : MetaM GateObl := do
    return { expr := ← mkForallFVars xs t, decoration := deco }
  let atom : MetaM (Array GateObl × Bool) := do return (#[← closed e false], false)
  if fuel == 0 then atom
  else match e.getAppFn.constName?.getD .anonymous, e.getAppArgs with
  | ``And, #[a, b] =>
    let (pa, sa) ← decomposeObls xs a (fuel - 1) directional
    let (pb, sb) ← decomposeObls xs b (fuel - 1) directional
    let mut out := pa ++ pb
    -- sides that split are also obligations as a whole (see the doc comment);
    -- an unsplit side already is its own single part
    if sa then out := out.push (← closed a false)
    if sb then out := out.push (← closed b false)
    return (out, true)
  | ``Iff, #[a, b] =>
    let (pa, sa) ← decomposeObls xs a (fuel - 1) directional
    let (pb, sb) ← decomposeObls xs b (fuel - 1) directional
    let mut out := pa ++ pb
    if sa then out := out.push (← closed a false)
    if sb then out := out.push (← closed b false)
    if directional then
      -- antecedent-side rescue patterns only: an antecedent asserting `A ↔ B`
      -- licenses a part `A → B` or `B → A` (shared content, not pollution)
      for arr in [← mkArrow a b, ← mkArrow b a] do
        out := out.push (← closed arr false)
        -- the synthesized arrow is decomposed too, so an iff-spelled antecedent
        -- yields `∀ xs, A → cᵢ` per conjunct like an implication-spelled one
        let (ps, _) ← decomposeObls xs arr (fuel - 1) directional
        out := out ++ ps
    return (out, true)
  | ``Exists, #[_, lam] =>
    if lam.isLambda then
      withLocalDecl lam.bindingName! lam.binderInfo lam.bindingDomain! fun x => do
        let (parts, split) ← decomposeObls (xs.push x) (lam.bindingBody!.instantiate1 x)
          (fuel - 1) directional
        -- an ∃ whose body does not split is an atom, not an obligation
        if split then return (parts, true) else atom
    else atom
  | _, _ =>
    if e.isForall then
      let d := e.bindingDomain!
      let dProp ← isPropSafe d
      withLocalDecl e.bindingName! e.binderInfo d fun x => do
        let (parts, split) ← decomposeObls (xs.push x) (e.bindingBody!.instantiate1 x)
          (fuel - 1) directional
        if dProp then
          let dec ← closed d true
          return (parts.push dec, split)
        else
          return (parts, split)
    else atom

/-- Open an obligation's leading non-Prop binders as fresh metavariables and
stop at the first Prop domain: stripping a Prop domain would let `(q → p)`
unify with a bare `p` and rescue a polluted part. Fresh metavariables let
binder-dependent shared content unify across binder order and naming. -/
partial def openNonPropBinders (e : Expr) : MetaM Expr := do
  if e.isForall then
    let d := e.bindingDomain!
    let dProp ← isPropSafe d
    if dProp then return e
    let m ← mkFreshExprMVar d
    openNonPropBinders (e.bindingBody!.instantiate1 m)
  else return e

/-- Counterpart rescue: does the closed obligation unify with any closed
antecedent pattern? Both sides open their non-Prop binders as fresh
metavariables in the same metavariable context. Flex-headed sides never
match (a Prop-quantified antecedent's bare `?P` would rescue everything).
Every try is rolled back and heartbeat-capped. -/
def matchesAntePattern (obl : Expr) (pats : Array Expr) : MetaM Bool := do
  for p in pats do
    let hit ← withoutModifyingState do
      orFalse <| withHeartbeats 2000 true do
        try
          let b ← openNonPropBinders obl
          let q ← openNonPropBinders p
          if b.getAppFn.isMVar || q.getAppFn.isMVar then pure false
          else isDefEq b q
        catch _ => pure false
    if hit then return true
  return false

/-- Antecedent-free provability, core arms (the ladder minus the antecedent):
definitional, structural close, restricted normalization. The
discovered-rewrite arm is `antefreeByRewrite`. -/
def antefreeProvableCore (obl : Expr) : MetaM Bool := do
  if ← goalDefeqTrue obl then return true
  let s ← saveState
  let ok ← try
    let g := (← mkFreshExprMVar obl).mvarId!
    let (_, g) ← g.intros
    pure (← structuralCore noAnteLemmas g).isEmpty
  catch _ => pure false
  restoreState s
  if ok then return true
  let s ← saveState
  let ok ← try
    let g := (← mkFreshExprMVar obl).mvarId!
    let (_, g) ← g.intros
    let ctx ← normalizationContext none
    let hyps ← g.getNondepPropHyps
    let (res, _) ← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := hyps)
    match res with
    | none => pure true
    | some (_, g') => pure (← structuralCore noAnteLemmas g').isEmpty
  catch _ => pure false
  restoreState s
  return ok

/-- Gate-side term normalization: the restricted normalization simp set
(plumbing and `push_cast`, no antecedent) applied to a statement as a term.
The ladder proves through this normalization, so the gate decomposes the
normalized form too: a pollutant behind one plumbing-removable wrapper
(`¬(A ∨ ¬q)` via `not_or` and `not_not`, `a ∈ {x | P x ∧ q}` via
`Set.mem_setOf_eq`) is invisible on the raw term. -/
def gateNormalize (t : Expr) : MetaM Expr := do
  try
    let ctx ← normalizationContext none
    let (r, _) ← Meta.simp t ctx
    pure r.expr
  catch _ => pure t

/-- All obligations of a goal: decompose the raw goal and its normalized form,
deduplicated structurally. Conjunct obligations only count when a genuine
split occurred somewhere (an unsplit conclusion is the whole goal, which the
triviality probe owns); decoration obligations always count. Normalization
cuts both ways: it can expose a wrapped pollutant, and if a simproc
normalizes a ground pollutant away (`2 + 2 = 4` to `True`) the raw
decomposition still carries it. -/
def gateObligations (goalType : Expr) : MetaM (Array GateObl) := do
  let collect (t : Expr) : MetaM (Array GateObl) := do
    let (obls, split) ← decomposeObls #[] t 6
    return if split then obls else obls.filter (·.decoration)
  let mut out ← collect goalType
  for o in ← collect (← gateNormalize goalType) do
    unless out.any (·.expr == o.expr) do out := out.push o
  return out

/-- The antecedent's own content, decomposed exactly like a goal (raw and
normalized, the same generalization over inner binders, so a shared
`∀ n, 6 ∣ n → 3 ∣ n` part matches shape for shape), split into two rescue
pools. `concl`, what the antecedent asserts (conclusion parts, sub-nodes and
the whole statement), rescues conjunct obligations. `hyps`, what the
antecedent merely assumes (its hypothesis domains at any depth), rescues only
decoration obligations, since an antecedent that assumes `q` never licenses
a candidate that asserts `q`. All patterns are closed terms; matching opens
binders per try. -/
structure AntePatterns where
  concl : Array Expr := #[]
  hyps : Array Expr := #[]

/-- The rescue patterns of the antecedent. `anteCanon?` is its canonical form
(side-local definitions unfolded, instances canonicalized), the form the goal
side is decomposed on; both the raw declaration type and the canonical form
are used, so a pattern never fails to match an obligation only because one
side has a local definition folded. Adding patterns can only rescue more
obligations, hence reject fewer, so a wrong pattern here admits pollution. -/
def anteGatePatterns (ante : Name) (anteCanon? : Option Expr := none)
    : MetaM AntePatterns := do
  let some info := (← getEnv).find? ante | return {}
  let add (arr : Array Expr) (e : Expr) : Array Expr :=
    if arr.contains e then arr else arr.push e
  let mut concl : Array Expr := #[]
  let mut hyps : Array Expr := #[]
  let baseForms := match anteCanon? with
    | some c => [info.type, c]
    | none   => [info.type]
  let mut forms : List Expr := []
  for b in baseForms do
    forms := forms ++ [b, ← gateNormalize b]
  for t in forms do
    concl := add concl t
    -- no split gating on the antecedent side: patterns are match targets, and
    -- the unsplit body ("the whole assertion") is a legitimate counterpart;
    -- `directional`: iff nodes also license their two implications
    let (obls, _) ← decomposeObls #[] t 6 (directional := true)
    for o in obls do
      if o.decoration then hyps := add hyps o.expr
      else concl := add concl o.expr
  return { concl, hyps }

/-- Discovery arm of the antecedent-free prober: can a single discovered
Eq/Iff rewrite close the obligation outright (rewrite to `rfl`, self-rewrite,
or rewrite then the structural closer)? Probe parity with the ladder:
candidates are discovered on the ∀-telescoped body and replayed after
`intros`, for every obligation, binder-dependent ones included, and a
conditional rewrite's side goals must also close without the antecedent, as
in the rw arms. The antecedent must be forbidden in the index: it is a
module-local theorem the module tree indexes, and an Iff-conclusioned
antecedent is a legal rewrite rule that would "prove" an obligation by
rewriting with itself. `forbid` is the role-independent union of both sides'
statement constants and must equal what the ladder's discovery forbids:
forbidding less would let the gate refute with a lemma the ladder cannot use,
forbidding more would let a disguised close slip past. -/
def antefreeByRewrite (forbid : NameSet) (obl : Expr)
    (moduleRef? : Option (Meta.LazyDiscrTree.ModuleDiscrTreeRef
                            (Name × Meta.Rewrites.RwDirection)) := none)
    : Term.TermElabM Bool := do
  try
    -- reuse the caller's tree when given one: building it is a real fold over
    -- the environment, and the gate calls this per obligation
    let moduleRef ← match moduleRef? with
      | some r => pure r
      | none   => Meta.Rewrites.createModuleTreeRef
    Meta.forallTelescope obl fun _ body => do
      let goal ← Meta.mkFreshExprMVar body
      -- the same absolute budget as the ladder's discovery (probe parity)
      let results ← withHeartbeats probeBudget false <| do
        Meta.Rewrites.findRewrites #[] moduleRef goal.mvarId! body
          (forbidden := forbid) (side := .none)
          (stopAtRfl := false) (max := (← getConfig).discoveryBudget) (leavePercentHeartbeats := 10)
      for r in results do
        if r.rfl? then return true
        let some lem := r.expr.getAppFn.constName? | continue
        if forbid.contains lem then continue
        let ok ← withoutModifyingState <| try
            let g := (← Meta.mkFreshExprMVar obl).mvarId!
            let (_, g) ← g.intros
            let tgt ← g.getType
            let rr ← g.rewrite tgt (← Meta.mkConstWithFreshMVarLevels lem) r.symm
            let g' ← g.replaceTargetEq rr.eNew rr.eqProof
            let sideRem ← structuralSolve noAnteLemmas rr.mvarIds
            if !sideRem.isEmpty then pure false
            else do
              let byRfl ← try
                  g'.refl
                  pure true
                catch _ => pure false
              if byRfl then pure true
              else pure (← structuralCore noAnteLemmas g').isEmpty
          catch _ => pure false
        if ok then return true
      return false
  catch _ => return false

/-- The relevance audit. A close must not merely depend on the antecedent;
the antecedent must do semantic work for every part of the goal, which rules
out a padded conjunct (`p` against `p ∧ 2 + 2 = 4`), a padded biconditional
side, a padded existential body and an unused true hypothesis (`p` against
`q → p`). Mechanism: the goal's conclusion is decomposed (through ∧ and ↔,
lifting x-free parts of ∃) into obligations; an obligation that does not
unify with any part of the antecedent's own statement (the counterpart
rescue, which protects shared content such as `p ∧ 0 < n` against
`p' ∧ 0 < n`) and is provable without the antecedent by the search's own
machinery (definitional, structural, restricted normalization, one
discovered rewrite) is pollution, and the close is rejected. Unused Prop
hypotheses are tested the same way. Fails open on internal errors. -/
def essentialUseAuditCore (ante : Name) (forbid : NameSet) (anteCanon : Expr)
    (goalType : Expr) (_proof : Expr)
    : Term.TermElabM (Option String) := do
  -- ablation switch (every consumer funnels through this function)
  if (← getConfig).noEssential then return none
  let trace := (← getConfig).trace
  try
    -- everything below shares one elaboration state: the patterns are closed
    -- terms and matching opens binders per try, and a single session is what
    -- makes that hold. One discrimination tree serves the whole audit.
    let auditTree ← Meta.Rewrites.createModuleTreeRef
    let pats ← anteGatePatterns ante (some anteCanon)
    let obls ← gateObligations goalType
    if obls.isEmpty then return none
    -- pass 1: counterpart rescue, pools split by obligation kind (an
    -- antecedent that merely assumes q never licenses a candidate that
    -- asserts q)
    let mut pending : Array GateObl := #[]
    let mut seen : Array Expr := #[]
    for obl in obls do
      if seen.contains obl.expr then continue
      seen := seen.push obl.expr
      let pool := if obl.decoration then pats.hyps ++ pats.concl else pats.concl
      unless ← matchesAntePattern obl.expr pool do
        pending := pending.push obl
    -- pass 2: the antecedent-free provability probe, per obligation capped; a
    -- bounded obligation count (traced, never silent) keeps pathological
    -- goals cheap
    let mut probed := 0
    for obl in pending do
      if probed ≥ 16 then
        if trace then
          IO.eprintln s!"[semanteq]   essential-use audit: obligation cap (16) hit, \
            {pending.size - probed} unchecked (fail-open)"
        break
      probed := probed + 1
      let provable ← orFalse <| withHeartbeats 25000 false do
        if ← antefreeProvableCore obl.expr then pure true
        else antefreeByRewrite forbid obl.expr (some auditTree)
      if provable then
        let kind := if obl.decoration then "hypothesis" else "conjunct"
        let pp := toString (← Meta.ppExpr obl.expr)
        return some s!"essential-use gate: {kind} `{takeChars pp 90}` is \
          provable without the antecedent (no relational evidence)"
    return none
  catch e =>
    -- fail open: the gate must not refuse genuine pairs on exotic goals, but
    -- never silently
    if trace then
      IO.eprintln s!"[semanteq]   essential-use audit error (fail-open): \
        {← e.toMessageData.toString}"
    return none

/-- Absolute heartbeat scope (option units) of one relevance-audit run,
covering the piecewise bound (sixteen obligations under the closer budget
plus sixteen discovery sweeps at `probeBudget`) with headroom. -/
def essentialUseGateBudget : Nat := 1500000

/-- `essentialUseAuditCore` in its own heartbeat scope, so the audit's cost is
bounded and invisible to the ladder: in the ambient scope it could drain a
direction's budget before any arm ran, and on accept a heartbeat kill would
be billed to the arm. Runtime kills are caught at this boundary too, failing
open with a trace line, the same policy as the core's own catch. -/
def essentialUseAudit (ante : Name) (forbid : NameSet) (anteCanon : Expr)
    (goalType : Expr) (proof : Expr) : Term.TermElabM (Option String) := do
  tryCatchRuntimeEx
    (withHeartbeats essentialUseGateBudget false
      (essentialUseAuditCore ante forbid anteCanon goalType proof))
    (fun e => do
      if (← getConfig).trace then
        IO.eprintln s!"[semanteq]   essential-use audit runtime kill \
          (fail-open): {← e.toMessageData.toString}"
      return none)
end SemantEq
