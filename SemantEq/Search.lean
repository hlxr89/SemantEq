import Lean
import SemantEq.Statement
import SemantEq.Gate
import SemantEq.Repackage
import SemantEq.Config
import SemantEq.Logic

/-!
# Bidirectional implication search

Each direction is judged in its own proving environment (`Context.lean`): the
antecedent statement is present as a named theorem, the target statement is
absent, and the goal is the target's statement type. Deriving the target from
the antecedent therefore means using the antecedent's name, the only
sanctioned way a proof may depend on a `sorry`-backed constant.

`proveDirectionTiered` runs one direction. Two checks precede the search: the
relevance audit (`Gate.lean`), run once per direction, refuses a goal that
has a part provable without the antecedent, and the triviality probe
(`goalDefeqTrue`) refuses a goal that is a definitional tautology, since such
a goal can carry no relational evidence. Then the ladder of attempts, each
audited as it produces a proof (`proveGoal`: proof-term grading, the
explosion check, the relevance audit):

1. the cheap closers: `intros; simp only [<ante>]`, the structural closer,
   normalization followed by the structural closer, the delayed-instance
   application of the antecedent, the structure-repackaging arm, and the
   restricted library search;
2. lemma discovery: the rewrite index is probed with both statements (their
   bodies and the domains of their Prop binders) for Eq/Iff-shaped bridge
   lemmas, both statements' own constants forbidden, plus the pair-directed
   transport lane (`discoverTransport`); the pool is computed once per pair
   and shared by both directions;
3. the bridge arms: every pool entry within the arm budget (ranked, the
   permutative and non-permutative families alternating) yields a
   `simp only [ℓ]` arm at hypotheses and target and a `rw [±ℓ] at *` arm,
   each finished by the structural closer under an antecedent-free replay;
   then one normalization arm with all of those entries at once; then, with
   `--depth` at least 2, the deep search over the harvested states; finally
   the goal-closing rewrites as audit bait, which close without the
   antecedent and land in `rejectedScripts` as an explicit
   library-provability trail.

Every accepted proof also passes the sorry audit: it may depend on the
antecedent, but reaching `sorryAx` any other way rejects it.
-/

namespace SemantEq
open Lean Elab

/-- Outcome of trying to prove one implication direction. -/
structure DirectionOutcome where
  closed          : Bool := false
  /-- Wall-clock time of this direction's search and audits, in milliseconds. -/
  elapsedMs       : Nat := 0
  /-- The closer (script or search step) that closed the goal. -/
  script          : String := ""
  /-- Did the proof term actually reach the antecedent constant? Required for
  a close. -/
  anteUsed        : Bool := false
  /-- The goal is a definitional tautology (`rfl`-closable). Triviality signal:
  such a direction says nothing about the pair's relationship. -/
  goalDefeqTrue   : Bool := false
  /-- Pretty-printed proof term (truncated when very large). -/
  proof           : String := ""
  /-- Constants the proof term actually depends on (audit input). -/
  usedConstants   : Array String := #[]
  /-- Attempts whose proof was rejected by an audit, with the reason. -/
  rejectedScripts : Array String := #[]
  /-- Attempts that produced no proof at all, so a record tells "nothing was
  attempted" apart from "every arm failed". -/
  failedScripts   : Array String := #[]
  /-- The discovered lemma pool of this direction, one entry per lemma as
  `"<lemma>|<orientation>|<origin>|p<probe>|r<rank>[|rfl]"`. -/
  discovered      : Array String := #[]
  /-- Number of composed pool-lemma steps in the winning arm: 0 for the fixed
  closers, 1 for single-rule arms, 2 or more for the deep search. The
  direction's bridge cost; `--depth` is the matching strength knob. -/
  bridgeDepth     : Nat := 0
  /-- Rejected proof terms (truncated), paired with `rejectedScripts` by
  index. -/
  rejectedProofs  : Array String := #[]
instance : ToJson DirectionOutcome where
  toJson d := Json.mkObj
    [ ("closed", Json.bool d.closed)
    , ("script", Json.str d.script)
    , ("anteUsed", Json.bool d.anteUsed)
    , ("elapsedMs", Lean.ToJson.toJson d.elapsedMs)
    , ("goalDefeqTrue", Json.bool d.goalDefeqTrue)
    , ("proof", Json.str d.proof)
    , ("usedConstants", Json.arr (d.usedConstants.map Json.str))
    , ("rejectedScripts", Json.arr (d.rejectedScripts.map Json.str))
    , ("failedScripts", Json.arr (d.failedScripts.map Json.str))
    , ("discovered", Json.arr (d.discovered.map Json.str))
    , ("rejectedProofs", Json.arr (d.rejectedProofs.map Json.str))
    , ("bridgeDepth", Json.num d.bridgeDepth) ]

/-- One discovered rewrite candidate, tagged with everything the arm builder
and the ranker need. -/
structure PoolEntry where
  lem    : Name
  /-- Apply right-to-left. -/
  symm   : Bool
  /-- This rewrite closed the goal outright: audit bait, not a closer, since it
  proves the goal is library-provable without the antecedent. -/
  rfl?   : Bool := false
  /-- Which probe surfaced it: 0 is the ∀-telescoped body, the only
  rw-reachable site; k > 0 is a binder domain or a connective side. -/
  probe  : Nat := 0
  /-- `"b-g"` or `"b-a"`: bridge probe of the goal's or the antecedent's type
  (assigned per direction from the discovery-time `"ref"`/`"cand"` tags);
  `"transport"`: the pair-directed lane. The default is always overwritten
  before ranking. -/
  origin : String := "rw"
  /-- Position in its probe's own result list; `findRewrites` returns
  candidates in discrimination-tree relevance order. -/
  rank   : Nat := 0
  /-- Discovered from both statements' pools: a cross-vocabulary bridge
  (`Nat.prime_iff` surfaces from `Prime` on one side and `Nat.Prime` on the
  other), the step material the deep search leads with. -/
  bothSides : Bool := false
  /-- Permutative: left and right sides identical up to a permutation of
  variables, as Lean's own classifier says (`SimpTheorem.perm`, the predicate
  `simp` consults to refuse a rewrite in the AC-increasing direction). So
  `perm = true` means `rw` can apply this and `simp` may refuse it, which is
  why the ranker puts these first. Comm-like only: `Nat.add_comm` and
  `Set.inter_comm` are permutative, `add_assoc` and `one_mul` are not. -/
  perm   : Bool := false
  /-- Fully instantiated lemma application of a transport bridge: two-sided
  anchoring pins carriers that one-sided evaluation leaves floating, so the
  arm must rewrite with this term (`IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ`,
  not the bare constant). Closed and environment-independent. -/
  inst?  : Option Expr := none
  deriving Repr

/-- Orientation-sensitive dedup key (`!f`/`!s` suffix). -/
def PoolEntry.key (e : PoolEntry) : Name :=
  e.lem.appendAfter (if e.symm then "!s" else "!f")

/-- Is this rewrite permutative in Lean's own sense? Delegates to
`SimpTheorem.perm`, the flag `simp` itself computes and consults before
refusing an AC-increasing rewrite. Fails closed (`false`) for anything
`mkSimpTheoremFromConst` cannot turn into a rewrite rule, a conservative
default since `false` only means "not ranked early". -/
def permOfLemma (lem : Name) (symm : Bool) : MetaM Bool := do
  try
    let ts ← Meta.mkSimpTheoremFromConst lem (post := true) (inv := symm)
    pure ((ts.map (·.perm)).any id)
  catch _ => pure false

/-- Order of the discovered pool. Permutative rewrites come first, since
`simp` may refuse them and only their `rw` arm can use them; then the
index's own relevance rank, which interleaves the probes instead of
exhausting one before the next; then the probe index (the telescoped body
before binder domains and connective sides); the origin is the final
tie-break, a bridge seen from the goal before one seen only from the
antecedent. -/
def PoolEntry.rankKey (e : PoolEntry) : Nat × Nat × Nat × Nat :=
  ( if e.perm then 0 else 1
  , e.rank
  , e.probe
  , match e.origin with | "b-g" => 1 | _ => 2 )

/-- Lexicographic `<` on `rankKey`, spelled out as a `Bool`: `qsort` wants a
`Bool`-valued comparator and the tuple's `<` is not usable as one. -/
def PoolEntry.rankLt (a b : PoolEntry) : Bool :=
  let (a1, a2, a3, a4) := a.rankKey
  let (b1, b2, b3, b4) := b.rankKey
  if a1 != b1 then a1 < b1
  else if a2 != b2 then a2 < b2
  else if a3 != b3 then a3 < b3
  else a4 < b4

/-- Run a `TermElabM` action in a given environment. -/
def runTermElabM (env : Environment) (opts : Options) (x : Term.TermElabM α) : IO α :=
  runMetaM env opts x.run'

/-- Elaborate one tactic script against `goalType`, keeping the failure
message when `withMessage` (the replay tool needs it; the ladder's attempts
skip the rendering). Multi-line scripts are laid out under an indented `by`
block, since inline `by {script}` breaks the layout parser for them. -/
def tryScriptE (goalType : Expr) (script : String) (withMessage : Bool := true)
    : Term.TermElabM (Except String Expr) := do
  let indented := String.intercalate "\n" ((script.splitOn "\n").map ("  " ++ ·))
  let src := s!"by\n{indented}"
  match Parser.runParserCategory (← getEnv) `term src with
  | .error e => return .error s!"PARSE: {e}"
  | .ok stx =>
    try
      -- align the file map with the script: paths that render the source at
      -- the parsed positions would otherwise hit mid-UTF-8 offsets
      withTheReader Core.Context (fun c => { c with fileMap := .ofString src }) do
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType stx goalType
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        if proof.hasSorry then return .error "ELAB: proof contains sorry"
        if proof.hasExprMVar then return .error "ELAB: unsolved metavariables"
        return .ok proof
    catch e =>
      if withMessage then return .error s!"ELAB: {← e.toMessageData.toString}"
      else return .error "ELAB"

/-- Try one tactic script against `goalType`; the proof term iff the script fully
closes the goal. Parse failures (tactic not available in this environment) and
tactic failures (including heartbeat timeouts) both yield `none`. -/
def tryScript (goalType : Expr) (script : String) : Term.TermElabM (Option Expr) :=
  (·.toOption) <$> tryScriptE goalType script (withMessage := false)

/-- Does `proof` reach the constant `target`? Every environment-local constant
is expanded (tactics hide their real dependencies inside `_proof_N`-style
auxiliaries), through the kernel environment for private ones. -/
partial def usesConstant (env : Environment) (target : Name) (proof : Expr) : Bool :=
  go proof.getUsedConstantsAsSet.toList {}
where
  go : List Name → NameSet → Bool
  | [], _ => false
  | c :: rest, visited =>
    if c == target then
      true
    else if visited.contains c then
      go rest visited
    else if isLocalConst env c then
      let extra := ((valueOf? env c).map (·.getUsedConstantsAsSet.toList)).getD []
      go (extra ++ rest) (visited.insert c)
    else
      go rest (visited.insert c)

/-- One ladder attempt: a label (recorded as the closing `script`) and an action
producing a proof of the goal type. Textual scripts and programmatic closers share
this shape. -/
structure Attempt where
  label : String
  run   : Term.TermElabM (Option Expr)

/-- Render a pool entry as a `rw`/`simp only` rule token. -/
def PoolEntry.arrow (e : PoolEntry) : String :=
  if e.symm then s!"← {e.lem}" else s!"{e.lem}"

/-- The `simp only [ℓ] at hyps` arm of one pool entry: shallow intros first
(stop before the first ordinary Prop hypothesis, so the implication survives
and the close can be a transplant), full intros as the fallback, inside one
attempt slot. The shallow try fails at once when the lemma has no match at
that depth. -/
def simpArm (goalType : Expr) (ante : Name) (e : PoolEntry)
    (harvest? : Option (IO.Ref (Array HarvestEntry)) := none) : Attempt :=
  let pairs := #[(e.lem, e.symm)]
  ⟨s!"simp only [{e.arrow}] at hyps/h_ante; simp only [{ante}]; <structural close>",
    do match ← Meta.MetaM.run' (bridgeAtHyps goalType ante pairs (shallow := true)
                  (harvest? := harvest?)) with
       | some p => pure (some p)
       | none => Meta.MetaM.run' (bridgeAtHyps goalType ante pairs (harvest? := harvest?))⟩

/-- The one multi-entry arm: plumbing normalization at hypotheses, then the
whole discovered pool against the normalized goal (a bridge that only matches
the normalized shape is unreachable from the raw goal). -/
def normalizeArm (goalType : Expr) (ante : Name) (entries : Array PoolEntry) : Attempt :=
  let rules := ", ".intercalate (entries.toList.map (·.arrow))
  ⟨s!"normalize (plumbing/cast); simp only [{rules}] at hyps; <structural close>",
    Meta.MetaM.run' (normalizeThenSolve goalType ante
      (bridges := entries.map fun e => (e.lem, e.symm)))⟩

/-- Bridge discovery for one statement: collect rewrite probes from its type,
the ∀-telescoped body plus the telescoped bodies of its Prop binder domains
(the statement's own hypotheses), and evaluate the rewrite index against
each. `findRewrites` evaluates candidates by rewriting, which fails under
binders; probing the telescoped bodies surfaces the bridges
(`Set.inter_comm` inside a quantified hypothesis) that the simp-based
hypothesis-side arm (`bridgeAtHyps`) can then reach. Called on both the
goal's type and the antecedent's. `forbid` is the role-independent union of
both sides' statement constants. -/
def discoverHypBridges (stmtType : Expr) (forbid : NameSet) (origin : String)
    (moduleRef : Meta.LazyDiscrTree.ModuleDiscrTreeRef (Name × Meta.Rewrites.RwDirection))
    (maxProbes : Nat := 6)
    (maxOut : Nat := 160) : Term.TermElabM (Array PoolEntry) := do
  try
    Meta.forallTelescope stmtType fun xs body => do
      -- the probe set: the stripped body and each Prop binder type, each
      -- telescoped again before evaluation
      let mut baseProbes : Array (Expr × Bool) := #[(body, true)]
      for x in xs do
        if baseProbes.size ≥ maxProbes then break
        let xty ← Meta.inferType x
        if ← Meta.isProp xty then
          baseProbes := baseProbes.push (xty, true)
      -- descend one level through the connectives: an `Iff`- or `And`-headed
      -- body hides its rewrite sites inside quantified sides
      -- (`(∀ x y, … n*n …) ↔ m ∈ S`) that top-level evaluation cannot reach
      let mut expanded := baseProbes
      for (probe, _) in baseProbes do
        if expanded.size ≥ 2 * maxProbes then break
        let inner ← Meta.forallTelescope probe fun _ pb => pure pb
        match inner.getAppFn.constName?.getD .anonymous, inner.getAppArgs with
        | ``Iff, #[a, b] => expanded := (expanded.push (a, true)).push (b, true)
        | ``And, #[a, b] => expanded := (expanded.push (a, true)).push (b, true)
        | ``Not, #[a] => expanded := expanded.push (a, true)
        | _, _ => pure ()
      -- probe 0: the statement re-closed over its binders from the first
      -- ordinary Prop hypothesis onward (instance binders stay open; their
      -- types are probed above). A full telescope eats the implication arrow
      -- that backward bridges (`not_imp`, `imp_forall_iff`) must match, so this
      -- probe is evaluated without re-telescoping.
      let mut probes := expanded
      let mut stopIdx := xs.size
      for k in [0:xs.size] do
        let decl ← xs[k]!.fvarId!.getDecl
        if (← Meta.isProp decl.type) && decl.binderInfo != .instImplicit then
          stopIdx := k
          break
      if stopIdx < xs.size then
        let stopped ← Meta.mkForallFVars (xs.extract stopIdx xs.size) body
        probes := #[(stopped, false)] ++ probes
      let mut seen : NameSet := {}
      let mut out : Array PoolEntry := #[]
      -- the probe index and the in-probe rank are the tags the ranker needs
      for probeIdx in [0:probes.size] do
        let (probe, tele) := probes[probeIdx]!
        if out.size ≥ maxOut then break
        -- every probe gets the same absolute budget (`probeBudget`)
        let hits ← try
          withHeartbeats probeBudget false <|
            if tele then
              Meta.forallTelescope probe fun _ pbody => do
                let goal ← Meta.mkFreshExprMVar pbody
                let db := (← getConfig).discoveryBudget
                Meta.Rewrites.findRewrites #[] moduleRef goal.mvarId! pbody
                  (forbidden := forbid)
                  (side := .none) (stopAtRfl := false)
                  (max := if probeIdx ≤ 1 then db else db / 4)
                  (leavePercentHeartbeats := 10)
            else do
              -- no telescope: the arrow is the rewrite target
              let goal ← Meta.mkFreshExprMVar probe
              let db := (← getConfig).discoveryBudget
              Meta.Rewrites.findRewrites #[] moduleRef goal.mvarId! probe
                (forbidden := forbid)
                (side := .none) (stopAtRfl := false)
                (max := if probeIdx ≤ 1 then db else db / 4)
                (leavePercentHeartbeats := 10)
        catch _ => pure []
        let mut rank := 0
        for r in hits do
          if out.size ≥ maxOut then break
          let some lem := r.expr.getAppFn.constName? | continue
          rank := rank + 1
          if r.rfl? then
            -- goal-closing rewrites from the body probes are kept as tagged
            -- entries: they get a bait script when this statement plays the
            -- goal, never an arm
            if probeIdx ≤ 1 then
              out := out.push { lem, symm := r.symm, rfl? := true, probe := probeIdx, origin, rank }
            continue
          if ← concretePattern lem r.symm then continue
          -- `perm` is filled in by a post-pass under its own budget: computing
          -- it here, inside the probe's budget, could abort the discovery
          let e : PoolEntry :=
            { lem, symm := r.symm, probe := probeIdx, origin, rank }
          unless seen.contains e.key do
            seen := seen.insert e.key
            out := out.push e
      return out
  catch e =>
    if (← getConfig).trace then
      IO.eprintln s!"[semanteq]   hyp-bridge discovery error: {← e.toMessageData.toString}"
    return #[]

/-- The pair-directed transport lane. Stage 1 queries the same discrimination
tree as ordinary discovery (`rwFindDecls`, the candidate step of
`findRewrites` without its evaluator) with both statements' closed
conclusions. Stage 2 anchors one Iff/Eq side of the candidate on each
statement's conclusion (both pairings, both orientations) and synthesizes the
leftover instance binders. Anchoring both sides pins the second carrier that
one-sided evaluation leaves floating and discards
(`IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ`). Residue policy: instance binders
only; an unassigned non-instance binder fails the candidate, since anything
looser turns discovery into a prover. Anchors must be closed: a statement
whose conclusion mentions its own binders is skipped. The relevance audit
cannot see these bridges (its probe is one rewrite, one-sided); the per-arm
antecedent-free replay covers the exposure. -/
def discoverTransport (refStmt candStmt : Expr) (forbid : NameSet)
    (moduleRef : Meta.LazyDiscrTree.ModuleDiscrTreeRef (Name × Meta.Rewrites.RwDirection))
    : MetaM (Array PoolEntry) := do
  let anchorsOf (stmt : Expr) : MetaM (Array Expr) :=
    Meta.forallTelescope stmt fun xs body => do
      let closed (e : Expr) : Bool := !xs.any (fun x => e.containsFVar x.fvarId!)
      let mut out : Array Expr := #[]
      if closed body then out := out.push body
      if let some inner := body.not? then
        if closed inner then out := out.push inner
      pure out
  let ra ← anchorsOf refStmt
  let ca ← anchorsOf candStmt
  if ra.isEmpty || ca.isEmpty then return #[]
  -- stage 1: candidate names from both statements' anchors, deduped
  let mut cands : Array Name := #[]
  let mut seenC : NameSet := {}
  for a in ra ++ ca do
    for (n, _, _) in ← Meta.Rewrites.rwFindDecls moduleRef a do
      unless seenC.contains n || forbid.contains n do
        seenC := seenC.insert n
        cands := cands.push n
  let sides (concl : Expr) : Option (Expr × Expr) :=
    if let some (l, r) := concl.iff? then some (l, r)
    else if let some (_, l, r) := concl.eq? then some (l, r)
    else none
  -- stage 2: two-sided anchoring and instance-only residue
  let mut out : Array PoolEntry := #[]
  for lem in cands do
    if out.size ≥ 6 then break
    let inst? ← withoutModifyingState do
      try
        let f ← Meta.mkConstWithFreshMVarLevels lem
        let (args, binfos, concl) ← Meta.forallMetaTelescope (← Meta.inferType f)
        let some (l, r) := sides concl | pure none
        let tryPairing (x y : Expr) : MetaM Bool := do
          if ← Meta.isDefEq l x then Meta.isDefEq r y else pure false
        let mut anchored := false
        for aR in ra do
          for aC in ca do
            unless anchored do
              -- cross-statement pairings only: one side per statement
              if ← (do let s ← saveState
                       if ← tryPairing aR aC then pure true
                       else do restoreState s
                               let s2 ← saveState
                               if ← tryPairing aC aR then pure true
                               else do restoreState s2; pure false) then
                anchored := true
        unless anchored do pure ()
        if !anchored then pure none else do
        -- residue: instances synthesized, nothing else may remain open
        let mut ok := true
        for h : i in [0:args.size] do
          let a := args[i]
          unless ← a.mvarId!.isAssigned do
            if binfos[i]! == .instImplicit then
              let aTy ← instantiateMVars (← a.mvarId!.getType)
              match ← Meta.trySynthInstance aTy with
              | .some v => unless ← Meta.isDefEq a v do ok := false
              | _ => ok := false
            else
              ok := false
        if !ok then pure none else do
        let e ← instantiateMVars (mkAppN f args)
        if e.hasExprMVar || e.hasSorry then pure none
        else pure (some e)
      catch _ => pure none
    if let some e := inst? then
      out := out.push { lem, symm := false, origin := "transport", inst? := some e }
  return out

/-- Run `attempts` in order; each runs in a fresh elaboration state. Every
proof is audited by the proof-term grading (`auditProof`: antecedent
required, all other used constants structural or Eq/Iff-grade), the
explosion check and the relevance audit. Rejections are recorded with their
reason; the first accepted proof is returned. -/
def proveGoal (env : Environment) (opts : Options) (ante : Name) (forbid : NameSet)
    (anteCanon : Expr)
    (goalType : Expr) (attempts : Array Attempt)
    (gateCache : IO.Ref (Option (Option String))) : IO DirectionOutcome := do
  let trace := (← getConfig).trace
  -- the relevance audit depends only on the antecedent and the goal, so it is
  -- computed at most once per direction; the cache is created by the caller
  -- and shared by both search phases
  let cachedEssentialUse (proof : Expr) : Term.TermElabM (Option String) := do
    match ← gateCache.get with
    | some v => pure v
    | none =>
      let v ← essentialUseAudit ante forbid anteCanon goalType proof
      gateCache.set (some v)
      pure v
  let mut rejectedScripts : Array String := #[]
  let mut failedScripts : Array String := #[]
  let mut rejectedProofs : Array String := #[]
  for attempt in attempts do
    let t0 ← IO.monoMsNow
    let mut escaped := false
    -- IO-level barrier: a pathological attempt (simp exceeding `maxRecDepth`)
    -- can escape the elaboration-level catch as an IO error; it must cost
    -- this attempt, not the batch
    let outcome? : Option (Except String DirectionOutcome) ← try
      runTermElabM env opts do
      match ← attempt.run with
      | none => pure none
      | some proof =>
        -- local auxiliaries are looked up in this attempt's post-elaboration environment
        let postEnv ← getEnv
        let verdict ← do
          match ← Meta.MetaM.run' (auditProof ante proof) with
          | some r => pure (some r)
          | none =>
            -- a self-contradictory antecedent closes any goal by ex falso,
            -- which is not a faithful correspondence
            match ← Meta.MetaM.run' (exFalsoVacuous? ante proof) with
            | some r => pure (some r)
            | none =>
              -- dependency is necessary but not sufficient: every part of
              -- the goal must need the antecedent
              cachedEssentialUse proof
        match verdict with
        | some reason =>
          let pp := toString (← Meta.ppExpr proof)
          let pp := if pp.length > 400 then takeChars pp 400 ++ " …[truncated]" else pp
          pure <| some <| Except.error s!"{attempt.label} ({reason})\u0000{pp}"
        | none =>
          -- the bridge depth from the arm label (an attempt carries no depth)
          let bridgeDepth : Nat :=
            if attempt.label.startsWith "deep search" then 2
            else if attempt.label.startsWith "simp only ["
                 || attempt.label.startsWith "intros; rw ["
                 || attempt.label.startsWith "normalize (plumbing/cast); simp only [" then 1
            else 0
          let anteUsed := usesConstant postEnv ante proof
          let pp := toString (← Meta.ppExpr proof)
          let pp := if pp.length > 2000 then takeChars pp 2000 ++ " …[truncated]" else pp
          let usedConstants := proof.getUsedConstantsAsSet.toArray.map (·.toString)
          pure <| some <| Except.ok { closed := true, script := attempt.label,
                                      anteUsed, proof := pp, usedConstants,
                                      bridgeDepth
                                      : DirectionOutcome }
    catch e =>
      if trace then
        IO.eprintln s!"[semanteq]     escaped IO error on `{takeChars attempt.label 80}`: {e}"
      -- record the death: an unrecorded heartbeat kill reads as "no arm fired"
      failedScripts := failedScripts.push
        s!"{attempt.label} (escaped: {takeChars (toString e) 150})"
      escaped := true
      pure none
    if trace then
      let status := match outcome? with
        | some (.ok _) => "closed"
        | some (.error _) => "rejected"
        | none => "failed"
      IO.eprintln s!"[semanteq]     {(← IO.monoMsNow) - t0}ms {status}: {takeChars attempt.label 120}"
    match outcome? with
    | some (.ok o) => return { o with rejectedScripts, failedScripts, rejectedProofs }
    | some (.error rejected) =>
      -- the reason and the proof term are joined by a null character above
      match rejected.splitOn "\u0000" with
      | [reason, pp] =>
        rejectedScripts := rejectedScripts.push reason
        rejectedProofs := rejectedProofs.push pp
      | _ =>
        rejectedScripts := rejectedScripts.push rejected
        rejectedProofs := rejectedProofs.push ""
    | none => unless escaped do failedScripts := failedScripts.push attempt.label
  return { rejectedScripts, failedScripts, rejectedProofs }

/-- Prove the target statement `goalType` from the antecedent theorem `ante`
(present in `env`; the target statement is absent by construction): the
relevance audit and the triviality probe, then the ladder (see the module
doc). -/
def proveDirectionTiered (env : Environment) (opts : Options) (goalType : Expr)
    (ante : Name) (forbid : NameSet) (anteCanon : Expr) (goalIsCand : Bool)
    (poolCache : IO.Ref (Option (Array PoolEntry × Array PoolEntry × Array PoolEntry)))
    : IO DirectionOutcome := do
  let trace := (← getConfig).trace
  -- every attempt gets a bounded heartbeat budget; discovery gets more room
  -- (it pays the lazy index build). `maxRecDepth` stays at Lean's default:
  -- raising it changes how far the normalization rewrites, which can move a
  -- statement past the point where its partner meets it
  let recDepth : Nat := 512
  let searchOpts := opts.set `maxHeartbeats (← getConfig).searchHeartbeats |>.set `maxRecDepth recDepth
  let discoveryOpts := opts.set `maxHeartbeats (1000000 : Nat) |>.set `maxRecDepth recDepth
  -- the triviality probe gates the search
  let defeqTrue ← try
    runTermElabM env searchOpts do
      pure (← goalDefeqTrue goalType)
  catch _ => pure false
  if trace && defeqTrue then
    IO.eprintln s!"[semanteq]   probes: goalDefeqTrue={defeqTrue}"
  -- the ladder
  let script (s : String) : Attempt := ⟨s, tryScript goalType s⟩
  -- the cheap closers run before any index sweep: most directions close here
  let mut phase1 : Array Attempt := #[
    script s!"intros; simp only [{ante}]",
    ⟨s!"structural solve_by_elim [{ante}, <structural>]", do
      let root ← Meta.mkFreshExprMVar goalType
      -- called directly (MetaM lifts into TermElabM): `MetaM.run'` would start
      -- a fresh metavariable context in which `root` does not exist
      structuralClose ante root.mvarId!⟩,
    ⟨"normalize (plumbing/cast) + structural", do
      Meta.MetaM.run' (normalizeThenSolve goalType ante)⟩,
    -- the delayed-instance application of the antecedent
    ⟨s!"intros; apply (allowSynthFailures) {ante}; <structural close>", do
      Meta.MetaM.run' (applyDelayedInstance goalType ante)⟩
  ]
  -- the structure-repackaging arm, a no-op unless a pair-local structure
  -- occurs in the goal or the antecedent (`repackagingClose`)
  phase1 := phase1.push
    ⟨"structure repackaging", do
      Meta.MetaM.run' (repackagingClose ante goalType)⟩
  -- the restricted library search is the last cheap closer: it needs nothing
  -- from discovery, so a direction it closes skips discovery altogether; its
  -- candidates are audited inside `restrictedSearch`
  phase1 := phase1.push
    ⟨"restricted exact?", do
      match ← Meta.MetaM.run' (restrictedSearch goalType ante) with
      | some (proof, _) => pure (some proof)
      | none => pure none⟩
  -- the discovery-derived arms are built below, only if the cheap closers fail
  let flags := fun (o : DirectionOutcome) => { o with goalDefeqTrue := defeqTrue }
  -- a definitionally trivial goal can carry no relational evidence: any
  -- antecedent can be laundered into such a proof through congruence lemmas
  -- (`Nat.add_right_cancel c : 2 = 2` proves `1 + 1 = 2` with the antecedent
  -- used but doing no work).
  -- one relevance verdict per direction, shared by both search phases
  let gateCache ← IO.mkRef (none : Option (Option String))
  -- the harvest of fired single-arm states and the depth a deep close used
  let harvestRef ← IO.mkRef (#[] : Array HarvestEntry)
  let depthRef ← IO.mkRef (0 : Nat)
  let nLemmaCap := (← getConfig).lemmaCap
  let nStateCap := (← getConfig).stateCap
  -- the relevance audit depends only on the antecedent and the goal, so it
  -- runs once before the ladder: a direction it refuses would have every arm
  -- rejected for the same reason, and its record then carries the single
  -- entry `pre-gated: <reason>` instead of per-arm labels. An exception in
  -- the audit falls through to the ladder. `SEMANTEQ_NO_PREGATE=1` turns the
  -- early run off.
  let preGate := !(← getConfig).noPregate
  -- `--depth`: 1 means single-lemma arms only, 2 enables the deep search
  let searchDepth := (← getConfig).depth
  let preGateVerdict ← if !preGate then pure none else
    try
      runTermElabM env searchOpts do
        let v ← essentialUseAudit ante forbid anteCanon goalType (mkConst ante)
        gateCache.set (some v)
        pure v
    catch _ => pure none
  let s ←
    if preGate && preGateVerdict.isSome then
      pure { rejectedScripts := #[s!"pre-gated: {preGateVerdict.get!}"]
             : DirectionOutcome }
    else if defeqTrue then
      pure { rejectedScripts := #["gated: goal is definitionally \
        trivial (no relational evidence possible)"] : DirectionOutcome }
    else do
      let s1 ← proveGoal env searchOpts ante forbid anteCanon goalType phase1 gateCache
      if s1.closed then
        pure s1
      else do
        -- discovery (pure data)
        let t0 ← IO.monoMsNow
        -- one pool per statement, computed lazily on the first need and
        -- cached per pair, so the second direction reuses it. Computing it in
        -- either direction's environment is sound: both proving environments
        -- contain both preambles, the index covers only public declarations,
        -- and both statement constants are forbidden, so the visible material
        -- is the same in either.
        let pools ← match ← poolCache.get with
          | some p => pure p
          | none =>
            let p ← try
              runTermElabM env discoveryOpts do
                let moduleRef ← Meta.Rewrites.createModuleTreeRef
                let refStmt  := if goalIsCand then anteCanon else goalType
                let candStmt := if goalIsCand then goalType else anteCanon
                let pr ← discoverHypBridges refStmt forbid "ref" moduleRef
                let pc ← discoverHypBridges candStmt forbid "cand" moduleRef
                -- `perm` is filled after the probes under its own budget, for
                -- the first 96 entries only (one classification per entry under
                -- one budget would abort wholesale on a big pool); the tail
                -- keeps `perm = false`
                let fillPerm (es : Array PoolEntry) : Term.TermElabM (Array PoolEntry) :=
                  withHeartbeats probeBudget false do
                    let mut out : Array PoolEntry := #[]
                    for i in [0:es.size] do
                      let some e := es[i]? | break
                      if i < 96 then
                        out := out.push { e with perm := ← permOfLemma e.lem e.symm }
                      else
                        out := out.push e
                    pure out
                let prF ← try fillPerm pr catch _ => pure pr
                let pcF ← try fillPerm pc catch _ => pure pc
                -- the transport lane is role-free (an Iff linking the two
                -- conclusions serves both directions), so it caches with the pools
                let pt ← try discoverTransport refStmt candStmt forbid moduleRef
                         catch _ => pure #[]
                pure (prF, pcF, pt)
            catch e =>
              if trace then
                IO.eprintln s!"[semanteq]   discovery escaped IO error: {e}"
              pure (#[], #[], #[])
            poolCache.set (some p)
            pure p
        -- the origin is a per-direction role tag ("b-g" the goal statement's
        -- pool, "b-a" the antecedent's), assigned here so the cached pools stay
        -- role-free
        let (poolR, poolC, poolT) := pools
        let goalPool := (if goalIsCand then poolC else poolR).map
          fun e => { e with origin := "b-g" }
        let antePool := (if goalIsCand then poolR else poolC).map
          fun e => { e with origin := "b-a" }
        -- the pair pool: the union, deduplicated by (lemma, orientation), goal
        -- side winning ties; the arm budget is the only limiter
        let mut seenK : NameSet := {}
        let mut pairPool : Array PoolEntry := #[]
        for e in goalPool ++ antePool do
          unless seenK.contains e.key do
            seenK := seenK.insert e.key
            pairPool := pairPool.push e
        -- transport entries enter in both orientations (which side of the
        -- pinned Iff faces the goal depends on the direction), same dedup key
        for e in poolT do
          for symm in [false, true] do
            let e' := { e with symm }
            unless seenK.contains e'.key do
              seenK := seenK.insert e'.key
              pairPool := pairPool.push e'
        -- cross-vocabulary bridges are marked by lemma name regardless of
        -- orientation: `Nat.prime_iff` surfaces as `←` from the `Prime` side
        -- and forward from the `Nat.Prime` side
        let goalNames : NameSet := goalPool.foldl (fun s e => s.insert e.lem) {}
        let anteNames : NameSet := antePool.foldl (fun s e => s.insert e.lem) {}
        pairPool := pairPool.map fun e =>
          { e with bothSides := goalNames.contains e.lem && anteNames.contains e.lem }
        -- the discovered pool, recorded as
        -- "<lemma>|<orientation>|<origin>|p<probe>|r<rank>[|rfl]"
        let pool : Array String :=
          pairPool.map fun e =>
            s!"{e.lem}|{if e.symm then "symm" else "fwd"}|{e.origin}|p{e.probe}|r{e.rank}{if e.rfl? then "|rfl" else ""}"
        if trace then
          IO.eprintln s!"[semanteq]   discovery: {(← IO.monoMsNow) - t0}ms, pair pool \
            {pairPool.size} (goal-side {(pairPool.filter (fun e => e.origin == "b-g")).size}, \
            rfl-bait {(pairPool.filter (fun e => e.rfl?)).size})"

        -- the discovery-derived arms
        let mut phase2 : Array Attempt := #[]
        -- every usable pool entry yields two arms, `simp only [ℓ]` at
        -- hypotheses and target (crosses binders, refuses permutative
        -- rewrites) and `rw [ℓ] at *` (one shot, applies permutative rules,
        -- cannot cross binders); the budget counts arms, so a lemma gets both
        -- tries or neither
        let usable := pairPool.filter fun e => !e.rfl?
        let rankedEntries := usable.qsort PoolEntry.rankLt
        -- the two ranked families alternate into the cap so neither
        -- monopolizes it; order within each family is preserved
        let armB := (← getConfig).armBudget
        let cappedEntries := Id.run do
          let cap := armB / 2
          let perms := rankedEntries.filter (·.perm)
          let nonPerms := rankedEntries.filter (!·.perm)
          let bound := min cap rankedEntries.size
          -- two non-permutative entries per round to one permutative
          let mut out : Array PoolEntry := #[]
          let mut i := 0
          let mut j := 0
          while out.size < bound do
            if out.size < bound then
              if let some e := nonPerms[j]? then out := out.push e
            if out.size < bound then
              if let some e := nonPerms[j+1]? then out := out.push e
            j := j + 2
            if out.size < bound then
              if let some e := perms[i]? then out := out.push e
            i := i + 1
          out
        if trace && rankedEntries.size > cappedEntries.size then
          IO.eprintln s!"[semanteq]   arm budget: {rankedEntries.size} pool entries \
            ranked, {rankedEntries.size - cappedEntries.size} dropped beyond {armB / 2}"
        -- the single-lemma arms harvest their fired states for the deep search
        let hv := if searchDepth ≥ 2 then some harvestRef else none
        -- the shallow `rwStar` stage exists for rewrites that need the goal's
        -- leading implication intact: the goal-side entries of probe 0, which
        -- is present only when the goal has an ordinary Prop binder. Every
        -- other entry rewrites material that survives full intros and runs
        -- once at full depth.
        let goalHasPropHyp ← try
            runTermElabM env searchOpts do
              Meta.forallTelescope goalType fun xs _ => do
                for x in xs do
                  let decl ← x.fvarId!.getDecl
                  if (← Meta.isProp decl.type) && decl.binderInfo != .instImplicit then
                    return true
                return false
          catch _ => pure true   -- fail-open: keep the two-stage behavior
        for e in cappedEntries do
          phase2 := phase2.push (simpArm goalType ante e (harvest? := hv))
          let staged := goalHasPropHyp && e.origin == "b-g" && e.probe == 0
          phase2 := phase2.push
            ⟨s!"intros; rw [{e.arrow}] at *; <structural close>",
              if staged then do
                match ← Meta.MetaM.run' (rwStar goalType ante e.lem e.symm (shallow := true)
                              (harvest? := hv) (proofOverride? := e.inst?)) with
                | some p => pure (some p)
                | none => Meta.MetaM.run' (rwStar goalType ante e.lem e.symm (harvest? := hv)
                              (proofOverride? := e.inst?))
              else
                Meta.MetaM.run' (rwStar goalType ante e.lem e.symm (harvest? := hv)
                  (proofOverride? := e.inst?))⟩
        unless cappedEntries.isEmpty do
          -- the one multi-entry arm: the pool against the normalized goal
          phase2 := phase2.push (normalizeArm goalType ante cappedEntries)
        -- the deep search comes last: it is the most expensive arm and pays
        -- off only when every single-rule arm has failed; it runs under its
        -- own heartbeat budget
        if searchDepth ≥ 2 && !cappedEntries.isEmpty then
          -- step candidates come from the full ranked pool: cross-vocabulary
          -- bridges first, then the rest in rank order, permutative shuffles
          -- last (a shuffle rarely enables a second bridge)
          let fullNonPerm := rankedEntries.filter fun e => !e.perm
          let step2List := ((fullNonPerm.filter fun e => e.bothSides)
            ++ (fullNonPerm.filter fun e => !e.bothSides)
            ++ rankedEntries.filter (fun e => e.perm)).map fun e => (e.lem, e.symm)
          phase2 := phase2.push
            ⟨s!"deep search (multi-depth ≤ {searchDepth})", do
              let harvest ← harvestRef.get
              -- the frontier is filled first come first served over the
              -- harvest reordered non-permutative first (stable within each
              -- class): composition wants bridges, not shuffles
              let permSet : NameSet := rankedEntries.foldl
                (fun st e => if e.perm then st.insert e.lem else st) {}
              let harvest := (harvest.filter fun h => !permSet.contains h.lem)
                ++ (harvest.filter fun h => permSet.contains h.lem)
              if harvest.isEmpty then pure none
              else
                match ← Meta.MetaM.run' (deepSearchLoop goalType ante harvest
                    step2List nLemmaCap nStateCap (← getConfig).deepLevelBudget searchDepth) with
                | some (p, d) => depthRef.set d; pure (some p)
                | none => pure none⟩
        -- audit bait: goal-side rewrites that close the goal outright close
        -- without the antecedent and land in `rejectedScripts` as an explicit
        -- library-provability trail
        phase2 := phase2 ++ (pairPool.filter fun e => e.rfl? && e.origin == "b-g").map
          (fun e => script s!"intros; rw [{e.arrow}]")
        let s2 ← proveGoal env searchOpts ante forbid anteCanon goalType phase2 gateCache
        pure { s2 with rejectedScripts := s1.rejectedScripts ++ s2.rejectedScripts
                     , failedScripts   := s1.failedScripts ++ s2.failedScripts
                     , rejectedProofs  := s1.rejectedProofs ++ s2.rejectedProofs
                     , discovered      := pool }
  if s.closed then
    -- a deep close's depth comes from the search; the label is static
    let s ← if s.script.startsWith "deep search" then
        pure { s with bridgeDepth := ← depthRef.get }
      else pure s
    return flags s
  return flags s

/-- Is `e` a `Prop`? Implication search only applies to propositions. -/
def isPropStatement (env : Environment) (opts : Options) (e : Expr) : IO Bool :=
  runMetaM env opts do
    return (← Meta.inferType e).isProp
end SemantEq
