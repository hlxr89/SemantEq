import Lean
import SemantEq.Statement
import SemantEq.RestrictedSearch
import SemantEq.Repackage
import SemantEq.Env

/-!
# Bidirectional implication search 

Each direction is judged in its own **proving environment** (`Context.lean`): the
antecedent statement is present as a genuine named theorem, the target statement is
absent, and the goal is the target's statement type itself. Deriving the target
*from the antecedent* therefore means literally using the antecedent's name, which
is the only sanctioned way a proof may depend on a `sorry`-backed constant.

**Probes** run first: `goalDefeqTrue` — the goal is a definitional tautology
(`rfl`-closable); `rfl` is NOT a closer (`1 = 1` and `2 = 2` are both
rfl-true and utterly unrelated). It sets a flag AND gates the strict tier;
`provableFromOwnHyps` is a reported flag only.
`provableFromOwnHyps` — the goal follows from its own hypotheses (BEq+'s vacuity
guard, surfaced as a flag).

**Strict tier** (drives the verdict) — antecedent-driven, restricted by
construction and by AUDIT v2 (`RestrictedSearch.auditProof`: the proof must reach
the antecedent, and every other used constant must be structural logic,
Eq/Iff-conclusioned, or exempt), applied to every candidate as it is produced:

1. `intros; simp only [<ante>]` — the antecedent as the sole rewrite rule;
2. **structural closer** (structural) — assert the antecedent into the context, add its
   replumbing variants (symm/mp/mpr/projections pushed under binders), forward-
   instantiate quantified hypotheses against the locals, saturate, `solveByElim`
   (covers apply/obtain/constructor/refine/⟨…⟩ and ∃/∧-reshuffle shapes);
3. **restricted `exact?`** — library search whose candidate finder only admits the
   antecedent, structural constants, and Eq/Iff-conclusioned lemmas; candidates
   stream through the audit one by one;
4. **pool arms**: one unified pool (bridges discovered by probing the goal's and
   the antecedent's statement types — bodies AND Prop binder domains, telescoped —
   plus the pair-directed transport lane); each entry yields two single-rule
   arms — `simp only [ℓ] at hyps/⊢` and `rw [±ℓ] at *` (`rwStar`) — each closed
   by the structural tail under an ante-free counterfactual replay;
5. **normalize-then-pool**: plumbing normalization at hypotheses + the discovered
   bridges in one pass (the only multi-entry arm at the defaults; the packed tail
   arm sits behind `enablePackedBridges := false`);
6. **restricted `apply?`** — as 3, but candidates leaving side goals are accepted
   when the structural closer finishes them (default-off:
   `enableRestrictedApply := false`);
7. bare `intros; rw [±lem]` for rewrites that close the goal outright — deliberate
   audit bait: they close without the antecedent and land in `rejectedScripts` as
   an explicit library-provability trail.

**Diagnostic tier** (fallback, BEq-grade evidence only): `omega`, `ring`,
`simp_all`, `exact?` — decision procedures and unrestricted library closure,
reported as `EquivalentUnrestricted`, with `anteUsed` recorded for the trail.

Every accepted proof also passes the sorry audit: it may depend on the antecedent,
but reaching `sorryAx` any other way rejects it.
-/

namespace SemantEq

open Lean Elab

/-- Outcome of trying to prove one implication direction. -/
structure DirectionOutcome where
  closed          : Bool := false
  /-- Wall-clock for this direction's whole search+audit, in ms . -/
  elapsedMs       : Nat := 0
  /-- The closer (script or search step) that closed the goal. -/
  script          : String := ""
  /-- Which ladder closed it: `"strict"` (antecedent-driven, audited) or
  `"diagnostic"` (decision procedures / library closure — BEq-grade evidence). -/
  tier            : String := ""
  /-- Did the proof term actually reach the antecedent constant? Required for a
  strict close; recorded (not required) on diagnostic closes. -/
  anteUsed        : Bool := false
  /-- The goal is a definitional tautology (`rfl`-closable). Triviality signal:
  such a direction says nothing about the pair's relationship. -/
  goalDefeqTrue   : Bool := false
  /-- The goal follows from its own hypotheses alone (BEq+ vacuity guard). -/
  provableFromOwnHyps : Bool := false
  /-- Pretty-printed proof term (truncated when very large). -/
  proof           : String := ""
  /-- Constants the proof term actually depends on (audit input). -/
  usedConstants   : Array String := #[]
  /-- Attempts whose proof was rejected by an audit, with the reason. -/
  rejectedScripts : Array String := #[]
  /-- Attempts that produced NO proof at all. Previously discarded
  (`| none => pure `), which made every JSONL record a LOWER BOUND on what was
  tried: an empty `rejectedScripts` could mean "nothing was attempted" or "20 arms
  ran and all failed", and the two are opposite diagnoses. -/
  failedScripts   : Array String := #[]
  /-- The discovered lemma pool for this direction, as
  `"<lemma>|<orientation>|<origin>|p<probe>|r<rank>[|rfl]"`. Without this,
  discovery is invisible: only lemmas that produced a proof ever appeared
  anywhere. -/
  discovered      : Array String := #[]
  /-- Number of composed pool-lemma steps in the winning arm: 0 for the
  fixed closers / diagnostic tier, 1 for single-rule arms, 2 for the deep search.
  This is the per-direction HONEST BRIDGE COST — the depth parameter is a strength
  parameter of the prover, and this field is its per-close measurement. -/
  bridgeDepth     : Nat := 0
  /-- Rejected proof TERMS (truncated), paired with `rejectedScripts` by
  index. `rejectedScripts` carries only the reason, so diagnosing WHY a gate fired
  meant guessing at the term — this is what forced the earlier analysis to infer. -/
  rejectedProofs  : Array String := #[]

instance : ToJson DirectionOutcome where
  toJson d := Json.mkObj
    [ ("closed", Json.bool d.closed)
    , ("script", Json.str d.script)
    , ("tier", Json.str d.tier)
    , ("anteUsed", Json.bool d.anteUsed)
    , ("elapsedMs", Lean.ToJson.toJson d.elapsedMs)
    , ("goalDefeqTrue", Json.bool d.goalDefeqTrue)
    , ("provableFromOwnHyps", Json.bool d.provableFromOwnHyps)
    , ("proof", Json.str d.proof)
    , ("usedConstants", Json.arr (d.usedConstants.map Json.str))
    , ("rejectedScripts", Json.arr (d.rejectedScripts.map Json.str))
    , ("failedScripts", Json.arr (d.failedScripts.map Json.str))
    , ("discovered", Json.arr (d.discovered.map Json.str))
    , ("rejectedProofs", Json.arr (d.rejectedProofs.map Json.str))
    , ("bridgeDepth", Json.num d.bridgeDepth) ]


/-- `restricted apply?` arm gate. **Default OFF**: it never
closed a direction. Flip to re-enable; `restrictedSearch`'s apply?-mode branch
(`exactMode := false`) is runtime-dead while this is false. -/
def enableRestrictedApply : Bool := false

/-- Pack ALL discovered bridges into ONE `simp only [...] at hyps` arm instead of
one arm per bridge. **Default OFF.** Packing produced
**0 new closes** across every suite (its 3 wins — `m42-not-exists`,
`m4-comm-honest`, `d4-set-ext` — all closed via per-lemma arms before it too) and
**cost 3**: one benchmark pair lost its accept, and two benchmark
directions stopped closing. Cause: signal density in a discovered bridge set is
only 7-22 % (`m4-comm-honest`: 1 real bridge in 14; `m42-not-exists`: winner ranked
17 of 18), so the noise rewrites past the shape the one real bridge needed. When
ON, the packed arm is appended as a TAIL arm after every per-lemma arm, where it
can add a close but never displace one. -/
def enablePackedBridges : Bool := false

/-- CLI-flag overrides for the per-direction env-read parameters (depth / lemma-cap
/ state-cap). `none` = fall through to the env var / default. -/
initialize depthOverrideRef : IO.Ref (Option Nat) ← IO.mkRef none
initialize lemmaCapOverrideRef : IO.Ref (Option Nat) ← IO.mkRef none
initialize stateCapOverrideRef : IO.Ref (Option Nat) ← IO.mkRef none

initialize discoveryBudgetRef : IO.Ref Nat ← do
  IO.mkRef (((← envVar "DISCOVERY_BUDGET").bind (·.toNat?)).getD 64)
/-- Capability-study width parameter : settable via env var at start or
`--discovery-budget` CLI flag; default 64 = shipped behavior. -/
def getDiscoveryBudget : BaseIO Nat := discoveryBudgetRef.get


/-- Absolute heartbeat budget for ONE discovery probe, in
`maxHeartbeats`-option units (1 unit = 1000 raw heartbeats).

Why this exists. `findRewrites`' own `leavePercentHeartbeats` guard is *relative to
the ambient remaining budget*: at 85 it aborts once 15 % of what is left has been
spent. The probes run sequentially inside one direction-wide discovery budget
(`discoveryOpts`, 1 000 000 units), so each probe got 15 % of an ever-shrinking
remainder — probe 1 got ~150 000 units, probe 12 ~21 000, a geometric decay. Two
consequences, both bad:

* **Late probes were starved**, so which lemmas reach the pool depended on probe
  ORDER rather than on relevance.
* **Pool content depended on ambient clock state** — how much budget earlier work
  happened to consume. That makes every pool-level A/B comparison unreliable: a
  changed pool cannot be attributed to the change under test rather than to load.
  (Live example: `trap:trivial_true:int_mul_vs_zero_le_one_real` flipped between
  `Inconclusive` and `LikelyTooWeak` across builds with no relevant code change.)

Giving each probe the SAME absolute allowance makes pool content a function of the
statement alone. The worst-case total stays bounded *deterministically* by
`probeBudget × probeCount`, and the probe count is already hard-capped
(`maxProbes`/`maxOut` for bridges, 16 obligations for the gate) — so no `min` against the ambient remaining is taken, which is the whole
point: `min` would reintroduce the clock dependence this removes.

The value matches one full ladder-attempt budget (50 000). With ≤ 21 bridge probes
per direction the ceiling is ~1 050 000 units, i.e. the ambient discovery budget it
replaces — so this equalizes the distribution without raising the total. -/
def probeBudget : Nat := 50000

/-- SET an absolute heartbeat budget for one probe (option units), regardless of
ambient — the `TermElabM`, any-result counterpart of `withHeartbeatBudget`.
Deliberately not min'd against the ambient remaining; see `probeBudget`. -/
def withProbeBudget {α : Type} (n : Nat) (x : Term.TermElabM α) : Term.TermElabM α := do
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context
    (fun c => { c with initHeartbeats := now, maxHeartbeats := n * 1000 }) x

/-- Where a pool entry's rule gets applied.

The rw/bridge split was historical, not designed — but the two
APPLICATIONS are genuinely different and must NOT be merged into one arm. Measured
on ProofNetVerif: `rw` winners are 32–36 % permutative (comm/unit/assoc) and **0 of 316**
cross a binder; bridge winners are 92 % `_iff`/`_def` and **59 of 132** do cross
one. The walls are structural, not incidental:

* `simp` **refuses permutative rules in the AC-increasing direction**
  (`Simp/Rewrite.lean:142-149` gates on `acLt`), so ~30 % of `rw`'s wins are
  unreachable by simp, ever;
* `rw` can **never** cross a binder (`KAbstract.lean:47-48` skips loose bvars);
* `rw` rewrites ONE instantiation, `simp` every one to fixpoint.

So what unifies is the DISCOVERY and the arm PLUMBING, not the tactic. -/
inductive PoolSite
  /-- Rewrite the goal's conclusion. -/
  | target
  /-- Rewrite every non-dependent Prop hypothesis, `h_ante` included (and, via
  `simplifyTarget`, the conclusion too). -/
  | hyps
  deriving BEq, Repr

/-- How a pool entry's rule gets applied. See `PoolSite`. -/
inductive PoolStrategy
  /-- `rw [±lem]` — one instantiation, survives simp loops, cannot cross binders. -/
  | rwOnce
  /-- `simp only [±lem]` — every instantiation to fixpoint, crosses binders,
  refuses AC-increasing permutative rewrites. -/
  | simpFix
  deriving BEq, Repr

/-- One discovered rewrite candidate, tagged with everything the arm
builder and the ranker need. Replaces the two bare `Array (Name × Bool)` channels
that the two discovery passes used to return independently. -/
structure PoolEntry where
  lem    : Name
  /-- Apply right-to-left. -/
  symm   : Bool
  /-- This rewrite closed the goal outright — audit bait, not a closer: it proves
  the goal is library-provable WITHOUT the antecedent. -/
  rfl?   : Bool := false
  /-- Which probe surfaced it. 0 = the ∀-telescoped body, i.e. the only
  rw-reachable site; k > 0 = a binder domain or a connective side. -/
  probe  : Nat := 0
  /-- `"b-g"`/`"b-a"` = bridge probe of the goal's / the antecedent's type
  (assigned per direction from the discovery-time `"ref"`/`"cand"` tags);
  `"transport"` = the pair-directed lane. The default is always overwritten
  before ranking. -/
  origin : String := "rw"
  /-- Position in its probe's own result list — `findRewrites` returns candidates
  in discrimination-tree relevance order. -/
  rank   : Nat := 0
  /-- this (lemma, orientation) was discovered from BOTH statements'
  pools — a cross-vocabulary bridge marker (`Nat.prime_iff` surfaces from `Prime`
  on one side and `Nat.Prime` on the other). The union dedup used to discard the
  duplicate silently, losing exactly the signal that identifies step material for
  the deep search. -/
  bothSides : Bool := false
  /-- Permutative: lhs and rhs are identical modulo permutation of variables.
  **populated from Lean's own classifier** (`SimpTheorem.perm`, via
  `mkSimpTheoremFromConst`) rather than a hand-rolled heuristic — it is the very
  predicate `simp` consults to refuse a rewrite in the AC-increasing direction
  (`Simp/Rewrite.lean:147`, `acLt`). So `perm = true` means *`rw` can apply this and
  `simp` may well refuse it*, which is why the ranker puts these first.

  NB this is comm-LIKE only: observed `Nat.add_comm`/`mul_comm`/`Set.inter_comm`
  → `true`, but `add_assoc` → `false` and `one_mul` → `false`. So it does not cover
  the whole "comm/unit/assoc" class that the rw-winner census lumped together. -/
  perm   : Bool := false
  /--  Fully-instantiated lemma application for a
  pair-directed TRANSPORT bridge — two-sided anchoring pinned carriers that
  one-sided evaluation leaves floating, so the bare constant is useless to
  `rw` and the arm must rewrite with THIS term (`IsFractionRing.isAlgebraic_iff
  ℤ ℚ ℝ`, not `IsFractionRing.isAlgebraic_iff`). Closed, env-independent. -/
  inst?  : Option Expr := none
  deriving Repr

/-- Orientation-sensitive dedup key, matching the `!f`/`!s` suffix scheme the
bridge merge has always used. -/
def PoolEntry.key (e : PoolEntry) : Name :=
  e.lem.appendAfter (if e.symm then "!s" else "!f")

/-- Is this rewrite permutative in Lean's own sense? Delegates to
`SimpTheorem.perm`, the flag `simp` itself computes (`isPerm lhs rhs`) and consults
before refusing an AC-increasing rewrite. Fails closed (`false`) for anything
`mkSimpTheoremFromConst` cannot turn into a rewrite rule — a conservative default,
since `false` only means "not ranked early". -/
def permOfLemma (lem : Name) (symm : Bool) : MetaM Bool := do
  try
    let ts ← Meta.mkSimpTheoremFromConst lem (post := true) (inv := symm)
    pure ((ts.map (·.perm)).any id)
  catch _ => pure false

/-- Per-direction cap on pool-derived arms. Before this the arm count
was the sum of two independent discovery caps (historical rw + bridge families),
so a saturated direction built ~88 arms in a fixed order determined by
which discovery family produced them — a *provenance* order, not a *promise* order.
Ranking makes the order meaningful, and only then is truncating it defensible. -/
initialize armBudgetRef : IO.Ref Nat ← do
  IO.mkRef (((← envVar "ARM_BUDGET").bind (·.toNat?)).getD 80)
/-- Capability-study width parameter: env var or `--arm-budget`; default 80. -/
def getArmBudget : BaseIO Nat := armBudgetRef.get

/-- Absolute heartbeat budget per deep-search LEVEL (option
units). Raised from a 400k whole-search budget : a level is
≤ nStateCap × nLemmaCap × 2 transforms plus a close per unseen state, and budget
death mid-level keeps partial results (best-first by rank). -/
initialize deepLevelBudgetRef : IO.Ref Nat ← do
  IO.mkRef (((← envVar "DEEP_LEVEL_BUDGET").bind (·.toNat?)).getD 1000000)
/-- Deep-search per-level heartbeat budget: env var or `--deep-level-budget`;
default 1M = shipped behavior. -/
def getDeepLevelBudget : BaseIO Nat := deepLevelBudgetRef.get

/-- Heartbeat cap (option units) for the search/closer phase (`searchOpts`).
Default 100k = shipped behavior — HALF of Lean's own 200k default, which is
measurably below the honest unification cost on research-grade statements: on
the shared-preamble mild corpus every structural arm dies at `whnf` timeout
(100000) while the hand witness (`exact ante hσ hB`) elaborates fine under
plain Lean defaults. Raise for big-statement corpora; failing arms burn
proportionally longer. Discovery keeps its own 1M cap. -/
initialize searchHeartbeatsRef : IO.Ref Nat ← do
  IO.mkRef (((← envVar "HEARTBEATS").bind (·.toNat?)).getD 100000)
/-- Search/closer heartbeat cap: env var or `--heartbeats`; default 100k. -/
def getSearchHeartbeats : BaseIO Nat := searchHeartbeatsRef.get

/-- Ranking key: permutative first, then earlier probes, then
goal-probe before ante-probe, then the index's own relevance order.

Rationale for each component, in priority order:
* `perm` first — these are the rewrites `simp` may structurally refuse, so if one is
  going to close the goal it will be via its `rw` arm and nothing else can substitute;
* `probe` ascending — probe 0 is the ∀-telescoped body, the only rw-reachable site;
  higher probes are binder domains and connective sides, i.e. progressively more
  speculative;
* `rank` ascending — `findRewrites` returns candidates in discrimination-tree
  relevance order, so this INTERLEAVES the families by their own relevance instead of
  exhausting one before starting the other;
* `origin` LAST, as a pure tie-break — a bridge seen from the goal outranks one seen
  only from the antecedent (≥84 % of bridge wins were reachable from the goal probe
  alone).

**Why `rank` must come before `origin`** — an empirical choice. With `origin`
third, every `rw` entry sorted ahead of every bridge entry, so on a direction with a
large rw pool the bridge arms were starved wholesale by the arm budget
(historical: the separate rw-discovery family was deleted in — all
entries are bridges today, so `origin` only separates goal-side from ante-side
and the `"rw" => 0` branch below is dead). That cost
one benchmark pair its accept for the third time: its `ref_to_cand` pool is 57 rw + 24
bridges, and the winning arm was the BRIDGE for `not_exists` (origin `b-g`, rank 5),
which sorted to position ≥58 and was dropped at 48. Bridges are 92 % `_iff`/`_def`
winners, so starving them is the most expensive thing this ranking could do. -/
def PoolEntry.rankKey (e : PoolEntry) : Nat × Nat × Nat × Nat :=
  ( if e.perm then 0 else 1
  , e.rank
  , e.probe
  , match e.origin with | "rw" => 0 | "b-g" => 1 | _ => 2 )

/- `rank` before `probe` — ROUND-ROBIN across probes, empirically. With `probe`
second, one deep probe monopolizes: first the goal side starved the ante side
(one benchmark pair's, concat merge), then the deep body probes starved probe 4 of the
same statement (same pairs again, arm conversion). Rank-first takes every probe's best
hit, then every probe's second hit — no probe can starve another, and the
discrimination tree's own relevance order is what interleaves them. -/

/-- Lexicographic `<` on `rankKey`, spelled out as a `Bool`: `qsort` wants a
`Bool`-valued comparator and the tuple's `<` is not usable as one. -/
def PoolEntry.rankLt (a b : PoolEntry) : Bool :=
  let (a1, a2, a3, a4) := a.rankKey
  let (b1, b2, b3, b4) := b.rankKey
  if a1 != b1 then a1 < b1
  else if a2 != b2 then a2 < b2
  else if a3 != b3 then a3 < b3
  else a4 < b4

/-- Diagnostic-only closers: unrestrictable decision procedures and library-closure
search. `omega` proves by contradiction over a linear-arithmetic certificate; `ring`
runs a hardwired polynomial normalizer; full `simp_all` pulls in the environment's
entire `@[simp]` set and simprocs; `exact?` closes with arbitrary library lemmas. -/
def diagnosticScripts : Array String := #[
  "intros; omega",
  "intros; ring",
  "intros; simp_all",
  "intros; exact?"
]

/-- Codepoint-safe truncation. `String.take` on this toolchain is byte-offset
`Slice`-based and PANICS on a mid-UTF-8 boundary (`String.Slice.pos!`) — labels
and pretty-printed goals are full of `←`/`∀`/`↑`, and this panic killed the
pollution suite at pair 26 . -/
def takeChars (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n)

/-- Run a `TermElabM` action in a given environment. -/
def runTermElabM (env : Environment) (opts : Options) (x : Term.TermElabM α) : IO α :=
  runMetaM env opts x.run'

/-- Try one tactic script against `goalType`; returns the proof term iff it fully
closes the goal. Parse failures (tactic not available in this environment) and tactic
failures (including heartbeat timeouts) both yield `none`. -/
def tryScript (goalType : Expr) (script : String) : Term.TermElabM (Option Expr) := do
  let src := s!"by {script}"
  match Parser.runParserCategory (← getEnv) `term src with
  | .error _ => return none
  | .ok stx =>
    try
      -- the parsed syntax carries positions into `src`, but the ambient
      -- fileMap is the fixture's; success paths that render the source at
      -- those positions (`exact?`'s Try-this suggestion → String.Slice.pos!)
      -- panic on mid-UTF-8 offsets. Align the map with the string .
      withTheReader Core.Context (fun c => { c with fileMap := .ofString src }) do
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType stx goalType
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        if proof.hasSorry || proof.hasExprMVar then
          return none
        return some proof
    catch _ =>
      return none

/-- Does `proof` reach `sorryAx` other than through an `allowed` constant (the
antecedent)? The walk expands every environment-local constant — tactics like `omega`
wrap their real dependencies inside freshly-declared auxiliary theorems
(`mkAuxTheorem` → `_proof_1`-style names), which must be looked through — but does not
look inside `allowed` constants: depending on the antecedent is the point. Returns the
offending constant. -/
partial def illegalDependency? (env : Environment) (allowed : NameSet) (proof : Expr)
    : Option Name :=
  go proof.getUsedConstantsAsSet.toList {}
where
  go : List Name → NameSet → Option Name
  | [], _ => none
  | c :: rest, visited =>
    if visited.contains c || allowed.contains c then
      go rest (visited.insert c)
    else if c == ``sorryAx then
      some c
    else if (env.getModuleIdxFor? c).isNone then
      -- kernel-env fallback: async/private auxiliaries have `value? = none` in the
      -- elab env (see `auditProof`); `#print axioms` resolves via the kernel env
      let extra := match env.toKernelEnv.find? c <|> env.find? c with
        | some info => (info.value?.map (·.getUsedConstantsAsSet.toList)).getD []
        | none => []
      go (extra ++ rest) (visited.insert c)
    else
      go rest (visited.insert c)

/-- Does `proof` reach the constant `target`? Same expansion discipline as
`illegalDependency?`. -/
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
    else if (env.getModuleIdxFor? c).isNone then
      -- kernel-env fallback: async/private auxiliaries have `value? = none` in the
      -- elab env (see `auditProof`); `#print axioms` resolves via the kernel env
      let extra := match env.toKernelEnv.find? c <|> env.find? c with
        | some info => (info.value?.map (·.getUsedConstantsAsSet.toList)).getD []
        | none => []
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

/-- THE arm builder: one function turning pool entries into an
`Attempt`, parameterized by `PoolSite` × `PoolStrategy` × an optional normalize
pre-pass. `bridgeAtHyps` and `normalizeThenSolve` are its instances; the rw
strategy lives OUTSIDE this builder as `rwStar` (`rw at *`), built inline by the
phase-2 ladder loop. : the dead `rwOnce` cells and their
closers (`rwThenStructural` — target-only rw; `rwAtHyps` — hyps-only rw) were
deleted; both had been unreachable since the arm conversion replaced
them with `rwStar`, and stale enough to mislead planning. The `PoolSite.target`
and `PoolStrategy.rwOnce` constructors remain as documentation of the design
space; the catch-all cell answers them visibly if ever re-wired.

**DESIGN INVARIANT — single-rule application.** `entries` is an array only because
the normalize arm has always taken the whole bridge set, and because
`enablePackedBridges` can append a packed tail arm. It is NOT a licence to pack:
signal density in a discovered bridge set is 7–22 % (`m4-comm-honest`: 1 real
bridge in 14; `m42-not-exists`: the winner ranked 17 of 18), so a multi-rule arm
can rewrite past the shape the one real bridge needed. Measured: packing won
nothing the per-lemma arms had not already won and cost 3 closes (three benchmark pairs, two of them
one benchmark pair's directions). **Callers must pass one entry per arm.** Enforcing
that here instead would break the two legitimate multi-entry arms, so the
invariant lives at the call site — where the arm loop is. -/
def applyPool (goalType : Expr) (ante : Name) (site : PoolSite)
    (strategy : PoolStrategy) (normalizePre : Bool) (entries : Array PoolEntry)
    (harvest? : Option (IO.Ref (Array HarvestEntry)) := none)
    : Attempt :=
  let rules := ", ".intercalate (entries.toList.map (·.arrow))
  let pairs := entries.map fun e => (e.lem, e.symm)
  match site, strategy, normalizePre, entries[0]? with
  | .hyps, .simpFix, false, some _ =>
    -- staged intros: SHALLOW first (stop before the first ordinary Prop
    -- hypothesis — the transplant route: the implication survives, the close can
    -- be an exact, no False is ever built), FULL as fallback, inside ONE attempt
    -- slot. The shallow try fails in microseconds when the lemma has no match at
    -- that depth, so the fallback path costs what the arm always cost.
    ⟨s!"simp only [{rules}] at hyps/h_ante; simp only [{ante}]; <structural close>",
      do match ← Meta.MetaM.run' (bridgeAtHyps goalType ante pairs (shallow := true)
                    (harvest? := harvest?)) with
         | some p => pure (some p)
         | none => Meta.MetaM.run' (bridgeAtHyps goalType ante pairs (harvest? := harvest?))⟩
  | .hyps, .simpFix, true, some _ =>
    ⟨s!"normalize (plumbing/cast); simp only [{rules}] at hyps; <structural close>",
      Meta.MetaM.run' (normalizeThenSolve goalType ante (bridges := pairs))⟩
  | _, _, _, _ =>
    -- unreachable from the ladder: an empty entry set, a retired `rwOnce`/`
    -- target` combination (see the doc comment), or `normalizePre` asked of a
    -- strategy that has no normalize-prefixed closer behind it.
    ⟨"[pool arm with no closer]", pure none⟩

/-- bridge discovery for the hypothesis side. Collect rewrite probes from a
statement type — the ∀-telescoped body plus the telescoped bodies of Prop-valued
binder domains (the statement's own hypotheses) — and evaluate the `rw?` index
against each. `findRewrites` evaluates candidates by actually rewriting, which
fails under binders; probing the telescoped bodies surfaces exactly the bridges
(e.g. `Set.inter_comm` inside a ∀-quantified hypothesis) that the simp-based
hypothesis-side application (`bridgeAtHyps`) can then reach. Called on BOTH the
goal's type and the antecedent's type.

`forbid` is the role-independent union of both sides' statement constants . -/
def discoverHypBridges (stmtType : Expr) (forbid : NameSet) (origin : String)
    (moduleRef : Meta.LazyDiscrTree.ModuleDiscrTreeRef (Name × Meta.Rewrites.RwDirection))
    (maxProbes : Nat := 6)
    (maxOut : Nat := 160) : Term.TermElabM (Array PoolEntry) := do
  try
    Meta.forallTelescope stmtType fun xs body => do
      -- today's probe set: the stripped body + each Prop binder type. Second
      -- component = telescope the probe again before evaluating (the historical
      -- behavior, right for ∀-quantified hypothesis types).
      let mut baseProbes : Array (Expr × Bool) := #[(body, true)]
      for x in xs do
        if baseProbes.size ≥ maxProbes then break
        let xty ← Meta.inferType x
        if ← Meta.isProp xty then
          baseProbes := baseProbes.push (xty, true)
      -- descend one level through logical connectives: an `Iff`/`And`-headed
      -- body hides its rewrite sites inside quantified sides (`(∀ x y, … n*n …)
      -- ↔ m ∈ S`) that top-level rw-evaluation can never reach
      let mut expanded := baseProbes
      for (probe, _) in baseProbes do
        if expanded.size ≥ 2 * maxProbes then break
        let inner ← Meta.forallTelescope probe fun _ pb => pure pb
        match inner.getAppFn.constName?.getD .anonymous, inner.getAppArgs with
        | ``Iff, #[a, b] => expanded := (expanded.push (a, true)).push (b, true)
        | ``And, #[a, b] => expanded := (expanded.push (a, true)).push (b, true)
        | ``Not, #[a] => expanded := expanded.push (a, true)
        | _, _ => pure ()
      -- probe 0 is the ARROW-PRESERVING suffix — the statement re-closed
      -- (`mkForallFVars`) over its binders from the first ORDINARY Prop hypothesis
      -- onward (instance binders like `[Nontrivial R]` stay open; their types are
      -- probed by the loop above, which is what makes `fact_iff` discoverable).
      -- Rationale: a full telescope eats the implication arrow that backward
      -- bridges (`not_imp`, `imp_forall_iff`, …) must match — the intros-depth
      -- gap, applied to discovery. Evaluated WITHOUT re-telescoping (flag
      -- `false`), or the arrow would be re-eaten at evaluation time. Purely
      -- ADDITIVE: everything the old probes reached is still probed above.
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
      -- carry the probe index and in-probe rank into the pool. Which
      -- probe surfaced a lemma is exactly the tag the ranker needs, and it was
      -- previously discarded at this line.
      for probeIdx in [0:probes.size] do
        let (probe, tele) := probes[probeIdx]!
        if out.size ≥ maxOut then break
        -- every probe gets the SAME absolute budget. Previously each got
        -- 15 % of the shrinking remainder, so probe 12 ran on ~1/7 of probe 1's
        -- allowance and the pool depended on probe ORDER, not relevance.
        let hits ← try
          withProbeBudget probeBudget <|
            if tele then
              Meta.forallTelescope probe fun _ pbody => do
                let goal ← Meta.mkFreshExprMVar pbody
                let db ← getDiscoveryBudget
                Meta.Rewrites.findRewrites #[] moduleRef goal.mvarId! pbody
                  (forbidden := forbid)
                  (side := .none) (stopAtRfl := false)
                  (max := if probeIdx ≤ 1 then db else db / 4)
                  (leavePercentHeartbeats := 10)
            else do
              -- no telescope — the arrow IS the rewrite target
              let goal ← Meta.mkFreshExprMVar probe
              let db ← getDiscoveryBudget
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
            -- keep goal-closing rewrites from the body probes as tagged
            -- entries — the old `rflTrail` audit bait, folded into the pool. They
            -- get a bait script when this statement plays GOAL, never a real arm.
            if probeIdx ≤ 1 then
              out := out.push { lem, symm := r.symm, rfl? := true, probe := probeIdx, origin, rank }
            continue
          if ← concretePattern lem r.symm then continue
          -- NB `perm` is deliberately NOT computed here: this loop runs inside the
          -- probe's heartbeat budget, and one `mkSimpTheoremFromConst`
          -- per candidate consumed enough of it to abort discovery outright —
          -- observed as one benchmark pair losing a direction with its pool going
          -- 81 -> 0. It is filled in by a post-pass under its own budget.
          let e : PoolEntry :=
            { lem, symm := r.symm, probe := probeIdx, origin, rank }
          unless seen.contains e.key do
            seen := seen.insert e.key
            out := out.push e
      return out
  catch e =>
    if (← envVar "TRACE").isSome then
      IO.eprintln s!"[semanteq]   hyp-bridge discovery error: {← e.toMessageData.toString}"
    return #[]

/-- ** — pair-directed transport lane (two-sided instantiation).**

Stage 1 queries the SAME discrimination tree as ordinary discovery
(`rwFindDecls` — `findRewrites`' own candidate step, minus its evaluator) with
BOTH statements' closed conclusions. Stage 2 is OUR evaluation: anchor one
Iff/Eq side of the candidate on each statement's conclusion (both pairings,
both orientations of anchors tried), then synthesize the leftover INSTANCE
binders. Both sides anchored means the pair itself pins the second carrier
that one-sided rw? evaluation leaves floating and therefore discards —
`IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ` on two benchmark pairs is the observed class.

Residue policy (charter): instance binders only — an unassigned non-instance
binder fails the candidate; anything looser turns discovery into a prover.
v1 restriction: anchors must be CLOSED (statements whose conclusion mentions
their own ∀-binders are skipped; the under-binder extension is future work).
The one-sided lanes are untouched — this lane only recovers their reject
class, so redundancy is structural-zero.

Gate parity note: the essential-use gate cannot see these bridges (its probe
is one-rewrite, one-sided); the per-arm counterfactual replay covers the
exposure — a transported goal that closes ante-free is rejected there. -/
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
  -- stage 2: two-sided anchoring + instance-only residue
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

/-- TermElabM heartbeat cap (same conversion as `withHeartbeatCap`, but
deliberately NOT min'd against the ambient remaining budget: this wraps the
essential-use audit, which runs AFTER the winning attempt has spent its search
budget — min'ing would starve the gate exactly on expensive closes, i.e. the
pollution would pass BECAUSE laundering it was costly. The audit is a post-hoc
verifier with its own bounded budget; the wall-clock cost is ≤ cap × obligation
count and only on accepted closes. -/
def withHeartbeatCapT (n : Nat) (x : Term.TermElabM Bool) : Term.TermElabM Bool := do
  let now ← IO.getNumHeartbeats
  tryCatchRuntimeEx
    (withTheReader Core.Context
      (fun c => { c with initHeartbeats := now, maxHeartbeats := n * 1000 }) x)
    (fun _ => pure false)

/-- Discovery arm of the ante-free prober: can a single discovered Eq/Iff
rewrite close the obligation outright (rewrite-to-rfl / self-rewrite / rewrite
then structural)? This is the route the pollution launderings actually used
(`Nat.prime_iff_card_units` → card equation → rfl; `Nat.even_iff` self-rewrite
→ `X ↔ X`). Probe parity with the ladder, v2: candidates are discovered on the
∀-telescoped body and replayed after `intros` — and the probe runs for ALL
obligations, not just fully-closed ones (v1 skipped binder-dependent parts,
but the ladder's own discovery is binder-aware: `∀ n, … ∧ n * 1 = n` was
ladder-provable via `mul_one` yet never probed — a verified parity break).
A conditional rewrite's side goals must ALSO close ante-free (mirroring the
counterfactual replay in the rw arms, today `rwStar`); v1 ignored `rr.mvarIds` and
could overclaim provability, wrongly gating a genuine pair.

The ANTECEDENT MUST BE FORBIDDEN in the index (as the ladder's own
the ladder's own discovery already does): the ante is a module-local theorem, so the
module tree indexes it, and an Iff-conclusioned ante is a legal rewrite rule —
v2 initially "proved" the (false!) obligation `∀ f n, n = 0 → f n = 0`
ante-free by rewriting with the ante `f n = 0 ↔ n = 0` itself, over-gating
m42-iff-split. v1 never tripped this only because it skipped binder-dependent
obligations entirely.

`forbid` is the role-independent union of both sides' statement constants
and MUST match what the ladder's own discovery forbids — probe parity. Forbidding
less here than the ladder does would let the gate refute with a lemma the ladder
was not allowed to use; forbidding more would let a laundered close slip past. -/
def antefreeByRewrite (forbid : NameSet) (obl : Expr)
    (moduleRef? : Option (Meta.LazyDiscrTree.ModuleDiscrTreeRef
                            (Name × Meta.Rewrites.RwDirection)) := none)
    : Term.TermElabM Bool := do
  try
    -- reuse the caller's tree when given one. `createModuleTreeRef`
    -- genuinely BUILDS the tree (`profileitM "build module discriminator tree"`),
    -- and the essential-use gate calls this per obligation — up to 16 rebuilds
    -- per gated direction.
    let moduleRef ← match moduleRef? with
      | some r => pure r
      | none   => Meta.Rewrites.createModuleTreeRef
    Meta.forallTelescope obl fun _ body => do
      let goal ← Meta.mkFreshExprMVar body
      -- absolute budget here too — PROBE PARITY. The gate's prober must
      -- see the same lemma yield as the ladder's own discovery, or a lemma the
      -- ladder can use to close becomes one the gate cannot use to refute.
      let results ← withProbeBudget probeBudget <| do
        Meta.Rewrites.findRewrites #[] moduleRef goal.mvarId! body
          (forbidden := forbid) (side := .none)
          (stopAtRfl := false) (max := (← getDiscoveryBudget)) (leavePercentHeartbeats := 10)
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

/-- **Essential-use gate .** A strict close must not merely *depend on*
the antecedent — the antecedent must be doing the semantic work for every part
of the goal. Verified escape patterns this closes (each with a compile-checked
false positive before the fix):

* **P1 ∧-pollution** — `p` vs `p ∧ q`, `q` ground/self-rewrite provable
  (`2+2=4` by rfl; `Nat.Prime 2` via `prime_iff_card_units`→rfl; a Mathlib
  Iff statement via self-rewrite). The close `⟨ante, rfl⟩` passes the
  dependency audit because the ante genuinely serves the shared conjunct.
* **P2 iff-side pollution** — `A ↔ B` vs `A ↔ (B ∧ q)`.
* **P3 ∃-lifted pollution** — `∃ x, P x` vs `∃ x, P x ∧ q`, `q` independent
  of `x`.
* **P4 hypothesis decoration** — `p` vs `q → p` with `q` ground-true: the
  intro'd hypothesis is unused and independently provable.

Mechanism: decompose the goal's conclusion (through ∧/↔, lifting x-free parts
of ∃) into obligations; an obligation that (a) does NOT unify with any part of
the antecedent's own statement (conclusion parts or hypothesis domains — the
*counterpart rescue*, protecting shared content like `p ∧ 0<n` vs `p' ∧ 0<n`)
and IS provable ante-free by the strict machinery minus the antecedent
(probe-parity: defeq/rfl, structural, restricted normalization, single
discovered rewrite) is pollution — the close is rejected. Same test for
unused Prop hypotheses (P4). Fail-open on internal errors: the gate protects
precision and must not silently destroy recall on exotic goals. -/
def essentialUseAuditCore (ante : Name) (forbid : NameSet) (anteCanon : Expr)
    (goalType : Expr) (_proof : Expr)
    : Term.TermElabM (Option String) := do
  -- ABLATION: essential-use audit off — covers the pre-gate,
  -- the strict on-accept fallback, and the diagnostic-tier v2 gate (all
  -- consumers funnel through this def).
  if (← envVar "NO_ESSENTIAL").isSome then return none
  let trace := (← envVar "TRACE").isSome
  try
    -- everything below shares the AMBIENT elaboration state — v1 wrapped each
    -- step in its own `Meta.MetaM.run'`, and pattern metavariables minted in
    -- one fresh mctx were matched in another: undefined behavior (unknown
    -- mvar-id panic path) for every quantified antecedent. The patterns are
    -- closed terms now and matching opens binders per-try, but single-session
    -- discipline is what makes that guarantee hold.
    -- ONE discrimination tree for the whole audit. `antefreeByRewrite`
    -- used to build its own per obligation — up to 16 tree builds per gated
    -- direction, each a real `createModuleDiscrTree` fold over the environment.
    let auditTree ← Meta.Rewrites.createModuleTreeRef
    let pats ← anteGatePatterns ante (some anteCanon)
    let obls ← gateObligations goalType
    if obls.isEmpty then return none
    -- pass 1: counterpart rescue, pools split by obligation kind (an ante
    -- that merely ASSUMES q never licenses a candidate that ASSERTS q)
    let mut pending : Array GateObl := #[]
    let mut seen : Array Expr := #[]
    for obl in obls do
      if seen.contains obl.expr then continue
      seen := seen.push obl.expr
      let pool := if obl.decoration then pats.hyps ++ pats.concl else pats.concl
      unless ← matchesAntePattern obl.expr pool do
        pending := pending.push obl
    -- pass 2: ante-free provability probe, per-obligation capped; bounded
    -- obligation count (traced, never silent) keeps pathological goals cheap
    let mut probed := 0
    for obl in pending do
      if probed ≥ 16 then
        if trace then
          IO.eprintln s!"[semanteq]   essential-use audit: obligation cap (16) hit, \
            {pending.size - probed} unchecked (fail-open)"
        break
      probed := probed + 1
      let provable ← withHeartbeatCapT 25000 do
        if ← antefreeProvableCore obl.expr then pure true
        else antefreeByRewrite forbid obl.expr (some auditTree)
      if provable then
        let kind := if obl.decoration then "hypothesis" else "conjunct"
        let pp := toString (← Meta.ppExpr obl.expr)
        return some s!"essential-use gate: {kind} `{takeChars pp 90}` is \
          provable without the antecedent (no relational evidence)"
    return none
  catch e =>
    -- fail-open: the gate protects precision and must not destroy recall on
    -- exotic goals — but never silently (the review's fail-open-abuse point)
    if trace then
      IO.eprintln s!"[semanteq]   essential-use audit error (fail-open): \
        {← e.toMessageData.toString}"
    return none

/-- Absolute heartbeat scope (option units) for ONE essential-use audit run.
Worst-case internal cost is already bounded piecewise (≤16 ablation
obligations × 25k closer budget + ≤16 discovery sweeps × `probeBudget`
≈ 1.2M units); this scope covers it with headroom. -/
def essentialUseGateBudget : Nat := 1500000

/-- Own-scope wrapper around `essentialUseAuditCore` . The audit
previously ran in the caller's AMBIENT scope: as the default-on PRE-gate it
drained the direction budget on research-grade statements before any arm ran
(every arm without a private reset then died at "timeout"), and on accept it
killed legitimate closes — the heartbeat kill escapes the elaboration-level
catch as an IO error and was billed to the ARM (observed: one research pair is
EquivalentRestricted in 269ms with the gate ablated, Inconclusive with it
on). The private scope makes the audit's cost bounded and invisible to the
ladder; runtime kills are caught at this boundary too — fail-open, traced,
same policy as the core's own catch. -/
def essentialUseAudit (ante : Name) (forbid : NameSet) (anteCanon : Expr)
    (goalType : Expr) (proof : Expr) : Term.TermElabM (Option String) := do
  tryCatchRuntimeEx
    (withProbeBudget essentialUseGateBudget
      (essentialUseAuditCore ante forbid anteCanon goalType proof))
    (fun e => do
      if (← envVar "TRACE").isSome then
        IO.eprintln s!"[semanteq]   essential-use audit runtime kill \
          (fail-open): {← e.toMessageData.toString}"
      return none)

/-- Run `attempts` in order; each runs in a fresh elaboration state. Every proof is
audited: strict tier via AUDIT v2 (`auditProof` — antecedent required, all other
used constants structural or Eq/Iff-grade), diagnostic tier via the sorry audit
only. Rejections are recorded with their reason; the first accepted proof wins. -/
def proveGoal (env : Environment) (opts : Options) (ante : Name) (forbid : NameSet)
    (assumed : NameSet) (anteCanon : Expr)
    (goalType : Expr) (attempts : Array Attempt) (strict : Bool)
    (gateCache : IO.Ref (Option (Option String))) : IO DirectionOutcome := do
  let trace := (← envVar "TRACE").isSome
  let allowed : NameSet := ({} : NameSet) |>.insert ante
  -- `essentialUseAudit` ignores its proof argument — it is a pure
  -- function of (ante, goalType) — yet it was re-run for EVERY accepted
  -- candidate (up to 92× per direction, each costing ≤16 × 25000 heartbeats plus
  -- ≤16 discovery sweeps). Compute it at most once per DIRECTION; the cache is
  -- created by the caller and shared across the strict and diagnostic passes.
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
    -- IO-level barrier: a pathological attempt (e.g. simp exceeding maxRecDepth)
    -- can escape the elaboration-level catch as an IO error; it must cost this
    -- attempt, not the batch.
    let outcome? : Option (Except String DirectionOutcome) ← try
      runTermElabM env opts do
      match ← attempt.run with
      | none => pure none
      | some proof =>
        -- look up local aux decls in the post-elaboration env of this attempt
        let postEnv ← getEnv
        let verdict ← do
          if strict then
            match ← Meta.MetaM.run' (auditProof ante proof (assumed := assumed)) with
            | some r => pure (some r)
            | none =>
              -- dependency can be VACUOUS — a self-contradictory
              -- antecedent closes any goal by ex-falso, which is not a faithful
              -- correspondence. One extra pass over the accepted proof term.
              match ← Meta.MetaM.run' (exFalsoVacuous? ante proof) with
              | some r => pure (some r)
              | none =>
                -- dependency is necessary but not sufficient — every part
                -- of the goal must need the antecedent (pollution check)
                cachedEssentialUse proof
          else
            match illegalDependency? postEnv (assumed.foldl (init := allowed) (·.insert ·)) proof with
            | some c => pure (some s!"reaches sorryAx via {c}")
            | none =>
              -- diagnostic anteUsed gate: BEq-grade evidence must still
              -- be *relational* — a close that never touches the antecedent
              -- only proves both statements are true, not that they are related
              if !(usesConstant postEnv ante proof) then
                pure (some "antecedent unused (diagnostic anteUsed gate)")
              else
                -- v2: reachability alone is launderable (`And.left` of a
                -- polluted ante counts as "used") — the essential-use audit
                -- gates this tier too, so gated pollution cannot relocate to
                -- EquivalentUnrestricted
                cachedEssentialUse proof
        match verdict with
        | some reason =>
          let pp := toString (← Meta.ppExpr proof)
          let pp := if pp.length > 400 then takeChars pp 400 ++ " …[truncated]" else pp
          pure <| some <| Except.error s!"{attempt.label} ({reason})\u0000{pp}"
        | none =>
          -- bridgeDepth from the arm label (Attempt has no depth field —
          -- the anonymous ⟨label, run⟩ constructor is used at ~15 sites; a
          -- label-prefix map here is the contained alternative)
          let bridgeDepth : Nat :=
            if attempt.label.startsWith "deep search" then 2
            else if attempt.label.startsWith "simp only ["
                 || attempt.label.startsWith "intros; rw ["
                 || attempt.label.startsWith "[packed]"
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
      -- the reason and the proof term are joined by NUL above; split them back out
      match rejected.splitOn "\u0000" with
      | [reason, pp] =>
        rejectedScripts := rejectedScripts.push reason
        rejectedProofs := rejectedProofs.push pp
      | _ =>
        rejectedScripts := rejectedScripts.push rejected
        rejectedProofs := rejectedProofs.push ""
    | none => unless escaped do failedScripts := failedScripts.push attempt.label
  return { rejectedScripts, failedScripts, rejectedProofs }

/-- Prove the target statement `goalType` from the antecedent theorem `ante` (present
in `env`; the target statement is absent by construction). Probes first (flags),
then the strict restricted ladder, then the diagnostic decision procedures. -/
def proveDirectionTiered (env : Environment) (opts : Options) (goalType : Expr)
    (ante : Name) (forbid : NameSet) (anteCanon : Expr) (goalIsCand : Bool)
    (poolCache : IO.Ref (Option (Array PoolEntry × Array PoolEntry × Array PoolEntry)))
    : IO DirectionOutcome := do
  let trace := (← envVar "TRACE").isSome
  -- Every single proof attempt gets a bounded heartbeat budget: a failing attempt
  -- must cost seconds, not the elaborator default's minutes. Discovery and the
  -- restricted searches get more room — they pay lazy discrimination-tree builds.
  -- maxRecDepth: deep simp congruence chains (rewriting under `∏`/`∑` binders
  -- with conditional-cast discharging) overrun the 512 default on real
  -- statements; this is a recursion guard, not a soundness bound
  -- maxRecDepth is raised ONLY for the transport/lift attempts (deep simp
  -- congruence under `∏`/`∑` binders overruns the 512 default). Raising it
  -- globally changes how far the base normalization rewrites, which can move a
  -- statement PAST the point where its partner meets it — the same normal-form
  -- instability that the transport layering exists to prevent.
  let recDepth := if enableM44Transport then (4096 : Nat) else (512 : Nat)
  let searchOpts := opts.set `maxHeartbeats (← getSearchHeartbeats) |>.set `maxRecDepth recDepth
  let discoveryOpts := opts.set `maxHeartbeats (1000000 : Nat) |>.set `maxRecDepth recDepth
  -- probes. `goalDefeqTrue` GATES the strict tier; `provableFromOwnHyps` is a
  -- reported FLAG only and computing it costs a full
  -- `structuralCore` run (enrichment + saturation + solveByElim depth 16) per
  -- direction. pay for it only when someone will actually read it, i.e.
  -- when tracing or when the env var restores it as a gate. The function itself
  -- is kept (diagnostics, and the gate can be switched back on).
  let wantOwnHyps := trace || (← envVar "OWNHYPS_GATE").isSome
  let (defeqTrue, ownHyps) ← try
    runTermElabM env searchOpts do
      pure (← goalDefeqTrue goalType,
            ← if wantOwnHyps then provableFromOwnHyps goalType else pure false)
  catch _ => pure (false, false)
  if trace && (defeqTrue || ownHyps) then
    IO.eprintln s!"[semanteq]   probes: goalDefeqTrue={defeqTrue} provableFromOwnHyps={ownHyps}"
  -- strict ladder
  let script (s : String) : Attempt := ⟨s, tryScript goalType s⟩
  -- carrier lifting: when goal and antecedent mention different numeric
  -- carriers, add normalize-attempts that lift both ends into a common larger
  -- carrier via the zify/qify/rify simp sets
  let liftTargets := if !enableM44Transport then [] else
    match env.find? ante with
    | some info => carrierLiftTargets goalType info.type
    | none => []
  -- PHASE 1 = the cheap closers, which win ~77% of all
  -- directions at ~2.5% of the wall time. They are built and run BEFORE the
  -- `rw?` discrimination-tree sweeps, because on directions that close early the
  -- sweeps were observed at 12-96% (median ~81%) of the direction's time and the
  -- winner never touched them.
  let mut phase1 : Array Attempt := #[
    script s!"intros; simp only [{ante}]",
    ⟨s!"structural solve_by_elim [{ante}, <structural>]", do
      let root ← Meta.mkFreshExprMVar goalType
      -- NB: call directly (MetaM lifts into TermElabM). `MetaM.run'` would
      -- start a FRESH metavariable context, in which `root` does not exist —
      -- the closer then proves a goal nobody is waiting for.
      if enableM44Transport then
        withHeartbeatBudget 120000 (structuralClose ante root.mvarId!)
      else
        structuralClose ante root.mvarId!⟩,
    ⟨"normalize (plumbing/cast) + structural", do
      Meta.MetaM.run' (normalizeThenSolve goalType ante)⟩,
    -- : delayed-instance ante application — see
    -- `applyDelayedInstance` (programmatic; ends in the same structural
    -- finisher as every arm; no tryScript).
    ⟨s!"intros; apply (allowSynthFailures) {ante}; <structural close>", do
      Meta.MetaM.run' (applyDelayedInstance goalType ante)⟩
  ]
  if enableM44Transport then
    phase1 := phase1.push
      ⟨"normalize (transport layer) + structural", do
        Meta.MetaM.run' (withHeartbeatBudget 120000
          (normalizeThenSolve goalType ante (transport := true)))⟩
  for (carrier, exts) in liftTargets do
    phase1 := phase1.push
      ⟨s!"carrier lift to {carrier} (zify-family + push_cast) + structural", do
        Meta.MetaM.run' (withHeartbeatBudget 120000
          (normalizeThenSolve goalType ante (extraExts := exts)
            (transport := true)))⟩
  -- structure repackaging (level 3,): the probe-B move for pairs
  -- whose preambles declare different-but-isomorphic structures. Gated inside
  -- `repackagingClose` on pair-local structure constants — a no-op for every
  -- other corpus.
  phase1 := phase1.push
    ⟨"structure repackaging", do
      Meta.MetaM.run' (repackagingClose ante goalType)⟩
  -- restricted `exact?` as the LAST cheap closer (moved from the phase-2 tail,
  -- design decision): it is ante-only — needs nothing from discovery —
  -- so a pair it closes skips discovery and the whole pool ladder. Audits run
  -- inside `restrictedSearch` on every streamed candidate, same as before.
  phase1 := phase1.push
    ⟨"restricted exact?", do
      match ← Meta.MetaM.run' (restrictedSearch goalType ante (exactMode := true)) with
      | some (proof, _) => pure (some proof)
      | none => pure none⟩
  -- PHASE 2 (built inline in the else-branch below, only if phase 1 fails).
  let flags := fun (o : DirectionOutcome) =>
    { o with goalDefeqTrue := defeqTrue, provableFromOwnHyps := ownHyps }
  -- Probe gate (BEq+'s guard, enforced): a goal that is definitionally trivial or
  -- follows from its own hypotheses can carry no relational evidence — ANY
  -- antecedent can be laundered into such a proof through whitelisted congruence
  -- lemmas (`Nat.add_right_cancel c : 2 = 2` proves the defeq-trivial `1+1 = 2`
  -- with `anteUsed = true` while the antecedent does no semantic work). Such a
  -- direction may still close on the diagnostic tier (BEq-grade), never strictly.
  -- : `provableFromOwnHyps` no longer GATES the strict tier —
  -- it stays a reported flag. It was an whole-goal probe with no
  -- rescue step, superseded by the essential-use gate, which first tries to
  -- RESCUE each obligation against what the antecedent asserts and only probes
  -- the un-rescued ones. Measured over 107 pairs (traps 28/28 resisted, 0
  -- CRITICAL, 0 BEq-grade; precision 0 FP; pollution 0 failures incl. all 6
  -- over-rejection controls; recall_fast 23/29): exactly ONE verdict moved, a
  -- trivial_true trap Inconclusive→LikelyTooWeak — still a rejection.
  -- Set SEMANTEQ_OWNHYPS_GATE=1 to restore it (probe-parity re-validation
  -- after any change that strengthens the closer, e.g. P1/P2).
  let ownHypsGate := (← envVar "OWNHYPS_GATE").isSome
  -- one essential-use verdict per DIRECTION, shared by both strict phases and
  -- the diagnostic tier 
  let gateCache ← IO.mkRef (none : Option (Option String))
  -- level-1 harvest (fired single-arm states, recorded by the arms
  -- themselves as they run) + the depth actually used by a deep close
  let harvestRef ← IO.mkRef (#[] : Array HarvestEntry)
  -- Fix 1: SEMANTEQ_TRUST_PREAMBLE — user-named preamble theorems (from
  -- EITHER side's preamble; both are in every proving env) become ASSUMED facts,
  -- sanctioned for sorry-dependence exactly like the antecedent. `anteUsed`
  -- still requires the real antecedent, so a preamble-only close stays
  -- rejected; internal-detail auxiliaries are excluded (audit blind spot
  -- otherwise); the essential-use prober shares the discovery index, so probe
  -- parity holds without extra work.
  let assumed : NameSet ←
    if (← envVar "TRUST_PREAMBLE").isSome then
      pure <| env.constants.map₂.foldl (init := ({} : NameSet)) fun st n ci =>
        match ci with
        | .thmInfo _ => if n.isInternalDetail || n == ante then st else st.insert n
        | _ => st
    else pure {}
  let depthRef ← IO.mkRef (0 : Nat)
  let nLemmaCap ← match ← lemmaCapOverrideRef.get with
    | some v => pure v
    | none => pure (((← envVar "LEMMA_CAP").bind (·.toNat?)).getD 24)
  let nStateCap ← match ← stateCapOverrideRef.get with
    | some v => pure v
    | none => pure (((← envVar "STATE_CAP").bind (·.toNat?)).getD 24)
  -- `essentialUseAudit` is a pure function
  -- of (ante, goalType) — it ignores its proof argument — so it can be evaluated
  -- BEFORE the ladder. When it fails the direction is refused anyway, so every arm
  -- that would then run is wasted: observed 1909 identical essential-use rejections
  -- over 21 pollution pairs (~90 per direction, all the same cached verdict).
  -- WHY THIS IS VERDICT-IDENTICAL, not merely verdict-identical-in-practice. The
  -- only material difference between the pre-attempt env and the env inside a
  -- winning attempt is the `_simp_N` auxiliaries that `simp only … at h` mints (one
  -- per call; `rw` mints none). Those are PRIVATE declarations, and
  -- `createModuleTreeRef` — the index behind `antefreeByRewrite`'s probe — excludes
  -- private decls. Verified by controlled probe: a PUBLIC env-local axiom IS found
  -- by `findRewrites`, an otherwise identical PRIVATE one is NOT, while the aux's
  -- own type is fully general (`∀ {a : Prop}, (¬¬a) = a`) so specificity is not the
  -- cause. So the probe's visible material is the same at every call site and the
  -- gate cannot change its answer with placement — in EITHER direction.
  -- Measured, pre-gate off vs on, instrumented: pollution 44:20 → 7:27
  -- (−83 %), recall_fast 8:24 → 8:40 (+3 %, one audit on directions that never
  -- close). Verdict changes: pollution 0/35, recall_fast 0/29, precision 0/15,
  -- traps 0/28 accept-level, gap examples 0/21 vs the de-packed baseline.
  -- COST: when the pre-gate refuses, no arm runs, so `rejectedScripts` loses the
  -- per-arm labels (the gate's own reason is still reported). Those labels were
  -- ~90 copies of one verdict, but a phase-1-only diagnostic sample (~2.5 % of a
  -- direction) remains available if that trail is wanted back. Opt out with
  -- SEMANTEQ_NO_PREGATE=1.
  let preGate := (← envVar "NO_PREGATE").isNone
  -- proof-search DEPTH parameter (a strength parameter alongside the
  -- discovery and arm budgets). Default 1 = single-lemma arms only, today's
  -- behavior. SEMANTEQ_DEPTH=2 enables the bounded depth-2 sequence search.
  let searchDepth ← match ← depthOverrideRef.get with
    | some v => pure v
    | none => pure (((← envVar "DEPTH").bind (·.toNat?)).getD 1)
  -- publish the ante decl for the e-match adapter (direction-scoped;
  -- phase-1 arms need it too, so it is set before any arm runs)
  if ← enableEMatchForward then ematchAnteRef.set (some ante)
  let preGateVerdict ← if !preGate then pure none else
    try
      runTermElabM env searchOpts do
        let v ← essentialUseAudit ante forbid anteCanon goalType (mkConst ante)
        gateCache.set (some v)
        pure v
    catch _ => pure none
  let s ←
    if preGate && preGateVerdict.isSome then
      pure { rejectedScripts := #[s!"strict tier PRE-gated: {preGateVerdict.get!}"]
             : DirectionOutcome }
    else if defeqTrue || (ownHyps && ownHypsGate) then
      pure { rejectedScripts := #["strict tier gated: goal is definitionally \
        trivial (no relational evidence possible)"] : DirectionOutcome }
    else do
      let s1 ← proveGoal env searchOpts ante forbid assumed anteCanon goalType phase1 (strict := true) gateCache
      if s1.closed then
        pure s1
      else do
        -- discovery (pure data)
        let t0 ← IO.monoMsNow
        -- ONE pool per STATEMENT, computed lazily on first phase-2 need
        -- and CACHED PER PAIR — the second direction reuses it (6 index sweeps per
        -- pair become 2). The pools are computed in whichever direction's env got
        -- here first; that is sound because both proving envs contain BOTH sides'
        -- preambles (each env = ante side in full + target side's preamble), the
        -- module tree indexes only public decls, and both statement constants are
        -- in the role-independent `forbid` — so the discovery-visible material is
        -- the same in either env.
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
                -- fill `perm` AFTER the probes, under its own budget
                -- (computing it inside discovery starved the probes).
                -- classify only the first 96 entries: the pool is no longer
                -- small (cap 160), and `mkSimpTheoremFromConst` per entry under
                -- one budget would abort wholesale on big pools, losing every
                -- perm tag. The tail keeps `perm = false` (= ranked later).
                let fillPerm (es : Array PoolEntry) : Term.TermElabM (Array PoolEntry) :=
                  withProbeBudget probeBudget do
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
                -- the pair-directed transport lane — role-free (an Iff
                -- linking the two conclusions serves both directions), so it
                -- caches with the pools.
                let pt ← try discoverTransport refStmt candStmt forbid moduleRef
                         catch _ => pure #[]
                pure (prF, pcF, pt)
            catch e =>
              if trace then
                IO.eprintln s!"[semanteq]   discovery escaped IO error: {e}"
              pure (#[], #[], #[])
            poolCache.set (some p)
            pure p
        -- role mapping for THIS direction; origin is a per-direction ROLE tag
        -- ("b-g" = the goal statement's pool, "b-a" = the antecedent's), assigned
        -- here rather than at discovery so the cached pools stay role-free.
        let (poolR, poolC, poolT) := pools
        let goalPool := (if goalIsCand then poolC else poolR).map
          fun e => { e with origin := "b-g" }
        let antePool := (if goalIsCand then poolR else poolC).map
          fun e => { e with origin := "b-a" }
        -- pair pool: union, deduped by (lemma, orientation), goal side winning
        -- ties. NO merge cap — the arm budget is the only limiter (the fixed
        -- 24-cap starved ante-side bridges the moment raised the goal side's
        -- yield; observed on both one benchmark pair's directions).
        let mut seenK : NameSet := {}
        let mut pairPool : Array PoolEntry := #[]
        for e in goalPool ++ antePool do
          unless seenK.contains e.key do
            seenK := seenK.insert e.key
            pairPool := pairPool.push e
        -- transport entries enter in BOTH orientations (which side of the
        -- pinned Iff faces the goal is direction-dependent), same dedup key.
        for e in poolT do
          for symm in [false, true] do
            let e' := { e with symm }
            unless seenK.contains e'.key do
              seenK := seenK.insert e'.key
              pairPool := pairPool.push e'
        -- mark cross-vocabulary bridges by LEMMA NAME, orientation-
        -- INSENSITIVE — the signature is precisely `Nat.prime_iff` surfacing as
        -- `←` from the `Prime` side and forward from the `Nat.Prime` side, so a
        -- keyed (lemma, orientation) collision never happens for exactly the
        -- entries this marker exists to find.
        let goalNames : NameSet := goalPool.foldl (fun s e => s.insert e.lem) {}
        let anteNames : NameSet := antePool.foldl (fun s e => s.insert e.lem) {}
        pairPool := pairPool.map fun e =>
          { e with bothSides := goalNames.contains e.lem && anteNames.contains e.lem }
        -- the discovered POOL, recorded so discovery is visible at all.
        -- Format: "<lemma>|<orientation>|<origin>|p<probe>|r<rank>[|rfl]".
        let pool : Array String :=
          pairPool.map fun e =>
            s!"{e.lem}|{if e.symm then "symm" else "fwd"}|{e.origin}|p{e.probe}|r{e.rank}{if e.rfl? then "|rfl" else ""}"
        if trace then
          IO.eprintln s!"[semanteq]   discovery: {(← IO.monoMsNow) - t0}ms, pair pool \
            {pairPool.size} (goal-side {(pairPool.filter (fun e => e.origin == "b-g")).size}, \
            rfl-bait {(pairPool.filter (fun e => e.rfl?)).size})"

        -- PHASE 2: the discovery-derived arms. `restricted exact?` is LAST of
        -- the real closers : it costs ~6.6% of wall time and burns its
        -- whole budget on a quarter of directions, for a ~1-3% win share, so it
        -- should only be paid once everything cheaper has failed. Verdicts are
        -- unaffected — the ladder returns on the first admissible proof.
        let mut phase2 : Array Attempt := #[]
        -- ARM CONVERSION (arm conversion): every usable pool entry yields exactly
        -- TWO arms — `simp only [ℓ] at hyps+target` (fixpoint; crosses binders,
        -- refuses AC-increasing permutative rewrites) then `rw [ℓ] at *` (one
        -- shot; applies permutative rules, cannot cross binders). Each strategy
        -- covers the other's structural refusals; mismatches fail fast.
        -- Single-rule invariant and per-arm counterfactual replay preserved.
        -- `armBudget` counts ARMS and entries are capped at armBudget/2, so a
        -- lemma gets both tries or neither — the budget cuts by LEMMA, never by
        -- strategy.
        let usable := pairPool.filter fun e => !e.rfl?
        let rankedEntries := usable.qsort PoolEntry.rankLt
        -- : perm-first stratification starved non-perm
        -- bridges wholesale once the pool exceeded the cap (the deep-search
        -- harvest learned this same lesson). Alternate the two ranked families
        -- into the cap so neither can monopolize it; order within each family
        -- is preserved.
        let armB ← getArmBudget
        let cappedEntries := Id.run do
          let cap := armB / 2
          let perms := rankedEntries.filter (·.perm)
          let nonPerms := rankedEntries.filter (!·.perm)
          let bound := min cap rankedEntries.size
          -- 2:1 bridge-weighted rounds: bridges are 92 % of observed winners
          -- (see the rankKey comment), so the non-perm family gets two slots
          -- per round to the perm family's one — a quota, not a monopoly.
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
        -- publish the top-K ranked bridges for the e-match adapter
        if ← enableEMatchForward then
          let k ← ematchK
          ematchBridgesRef.set (cappedEntries[0:min k cappedEntries.size].toArray.map
            fun e => (e.lem, e.symm))
        if trace && rankedEntries.size > cappedEntries.size then
          IO.eprintln s!"[semanteq]   arm budget: {rankedEntries.size} pool entries \
            ranked, {rankedEntries.size - cappedEntries.size} dropped beyond {armB / 2}"
        -- single-lemma arms harvest their fired states as they run
        -- (level 1 of the deep search, collected BEFORE knowing whether any
        -- level-1 close succeeds; a success discards the harvest for free)
        let hv := if searchDepth ≥ 2 then some harvestRef else none
        -- : probe-0-conditioned rwStar staging. The shallow
        -- (`introsToFirstPropHyp`) stage exists for rewrites that need the goal's
        -- leading implication intact — exactly the b-g entries surfaced by the
        -- arrow-preserving suffix probe, which is prepended as probe 0 only
        -- when the goal has an ordinary Prop binder. Everywhere else the shallow
        -- try was duplicate cost, worst when it FIRED but failed to close (a
        -- second full `structuralCore` on the fallback), and with no ordinary
        -- Prop binder `introsToFirstPropHyp` ≡ full `intros`, so the arm ran
        -- twice VERBATIM. Ante-side and telescoped-probe entries rewrite
        -- material that survives full intros (hypotheses keep their statement
        -- shape; closed patterns match under a non-dependent arrow), so they
        -- run once at full depth. Depth agreement with discovery is inherited,
        -- not enforced: the depth is chosen by where discovery matched.
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
          phase2 := phase2.push (applyPool goalType ante .hyps .simpFix false #[e]
            (harvest? := hv))
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
          -- the one legitimate multi-entry arm: the pool against the NORMALIZED
          -- goal (see RecallPlan P1(d)); appended after every per-lemma arm.
          phase2 := phase2.push (applyPool goalType ante .hyps .simpFix true cappedEntries)
          -- TAIL arm, flag-gated: the packed variant (see `enablePackedBridges`).
          if enablePackedBridges then
            let packed := applyPool goalType ante .hyps .simpFix false cappedEntries
            phase2 := phase2.push { packed with label := s!"[packed] {packed.label}" }
        -- (restricted `exact?` moved to the phase-1 tail, — see above.)
        if enableRestrictedApply then
          phase2 := phase2.push
            ⟨"restricted apply?", do
              match ← Meta.MetaM.run' (restrictedSearch goalType ante (exactMode := false)) with
              | some (proof, _) => pure (some proof)
              | none => pure none⟩
        -- the deep arm — LAST of the strict arms (it is the most
        -- expensive and only pays off when every single-rule arm has failed).
        -- Shallow-first then full, one slot; own heartbeat budget (the ambient
        -- per-attempt 50k would die mid-census).
        if searchDepth ≥ 2 && !cappedEntries.isEmpty then
          -- level-2+ candidates come from the FULL ranked pool, not
          -- the top-32 arm cap (the needed second orientation was observed to
          -- rank below it — `← Nat.prime_iff` in the largest pair's cand→ref).
          -- Cross-vocabulary bridges (discovered from BOTH statements' pools,
          -- orientation-insensitively) lead, then the rest in rank order, perm
          -- shuffles last — perm-first is right for single-rw arms and wrong for
          -- composition (a shuffle rarely ENABLES a second bridge).
          let fullNonPerm := rankedEntries.filter fun e => !e.perm
          let step2List := ((fullNonPerm.filter fun e => e.bothSides)
            ++ (fullNonPerm.filter fun e => !e.bothSides)
            ++ rankedEntries.filter (fun e => e.perm)).map fun e => (e.lem, e.symm)
          phase2 := phase2.push
            ⟨s!"deep search (multi-depth ≤ {searchDepth})", do
              let harvest ← harvestRef.get
              -- frontier selection is FCFS — but over the harvest reordered
              -- NON-PERM FIRST (stable within each class, so rank order is
              -- preserved). The raw harvest arrives in ARM order, which is
              -- perm-first; observed on the largest pair, that fills all frontier
              -- slots with `mul_comm`-class shuffle states and burns the level
              -- budget on their junk closes. Composition step 1 wants bridges,
              -- not shuffles — the same lesson as the v1 census, third time.
              let permSet : NameSet := rankedEntries.foldl
                (fun st e => if e.perm then st.insert e.lem else st) {}
              let harvest := (harvest.filter fun h => !permSet.contains h.lem)
                ++ (harvest.filter fun h => permSet.contains h.lem)
              if harvest.isEmpty then pure none
              else
                match ← Meta.MetaM.run' (deepSearchLoop goalType ante harvest
                    step2List nLemmaCap nStateCap (← getDeepLevelBudget) searchDepth
                    (rdForbid := forbid)) with
                | some (p, d) => depthRef.set d; pure (some p)
                | none => pure none⟩
        -- audit bait: goal-side rewrites that close the goal outright (the old
        -- rflTrail) — they close WITHOUT the antecedent and land in
        -- rejectedScripts as an explicit library-provability trail.
        phase2 := phase2 ++ (pairPool.filter fun e => e.rfl? && e.origin == "b-g").map
          (fun e => script s!"intros; rw [{e.arrow}]")
        let s2 ← proveGoal env searchOpts ante forbid assumed anteCanon goalType phase2 (strict := true) gateCache
        pure { s2 with rejectedScripts := s1.rejectedScripts ++ s2.rejectedScripts
                     , failedScripts   := s1.failedScripts ++ s2.failedScripts
                     , rejectedProofs  := s1.rejectedProofs ++ s2.rejectedProofs
                     , discovered      := pool }
  if s.closed then
    -- a deep close's TRUE depth comes from the search (the label map
    -- in `proveGoal` cannot know it — the label is static)
    let s ← if s.script.startsWith "deep search" then
        pure { s with bridgeDepth := ← depthRef.get }
      else pure s
    return flags { s with tier := "strict" }
  -- the diagnostic tier (decision-procedure closes reported as
  -- `EquivalentUnrestricted`) is RETIRED — BEq-grade evidence carries no
  -- information this evaluator stands behind, so failing strict directions
  -- return as-is instead of paying the decision-procedure pass.
  return flags s

/-- Is `e` a `Prop`? Implication search only applies to propositions. -/
def isPropStatement (env : Environment) (opts : Options) (e : Expr) : IO Bool :=
  runMetaM env opts do
    return (← Meta.inferType e).isProp

end SemantEq
