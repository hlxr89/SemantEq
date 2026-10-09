import Lean

/-!
# Configuration

Everything the two programs read from the environment (`SEMANTEQ_<NAME>`) or
from the command line, read once at start-up into `configRef`. A command-line
flag overrides the corresponding variable. An on/off switch is on when set to
anything but the empty string, `0` or `false`.
-/

namespace SemantEq

/-- Read a configuration variable `SEMANTEQ_<name>`. -/
def envVar (name : String) : IO (Option String) :=
  IO.getEnv s!"SEMANTEQ_{name}"

/-- An on/off switch `SEMANTEQ_<name>`: on when set to anything but the empty
string, `0` or `false`. -/
def envSwitch (name : String) : IO Bool := do
  match ← envVar name with
  | some v => return v != "" && v != "0" && v != "false"
  | none => return false

/-- A numeric variable `SEMANTEQ_<name>`, `default` when unset or not a number. -/
def envNat (name : String) (default : Nat) : IO Nat := do
  return ((← envVar name).bind (·.toNat?)).getD default

structure Config where
  -- search strength of the evaluator
  /-- maximum length of multi-step bridge sequences; 1 = single-lemma arms only -/
  depth : Nat := 1
  /-- deep search: candidate lemmas per level -/
  lemmaCap : Nat := 24
  /-- deep search: frontier width -/
  stateCap : Nat := 24
  /-- rewrite-index hits per discovery probe -/
  discoveryBudget : Nat := 64
  /-- how many top-ranked discovered lemmas become proof arms -/
  armBudget : Nat := 80
  /-- deep search: heartbeat budget per level (option units) -/
  deepLevelBudget : Nat := 1000000
  /-- heartbeat cap of the search/closer phase (option units) -/
  searchHeartbeats : Nat := 100000
  /-- wall-clock limit per pair in seconds for the evaluator; 0 = none -/
  timeoutSecs : Nat := 20
  /-- distinct base environments allowed per process (each costs gigabytes) -/
  maxEnvs : Nat := 4
  -- output and modes
  /-- print JSON records instead of the readable summary -/
  raw : Bool := false
  /-- the checker's strict reading: every severe use fails the proof -/
  strict : Bool := false
  /-- progress and diagnostic lines on stderr -/
  trace : Bool := false
  /-- the checker's per-decision trace -/
  auditTrace : Bool := false
  -- the evaluator's ablation switches, each turning one audit off
  /-- do not run the relevance audit before the search; it still runs on
  every accepted proof (`SEMANTEQ_NO_PREGATE`) -/
  noPregate : Bool := false
  /-- turn the relevance audit off (`SEMANTEQ_NO_ESSENTIAL`) -/
  noEssential : Bool := false
  /-- turn the explosion check off, so a proof that closes the goal from a
  constructed `False` is not refused (`SEMANTEQ_NO_P0`) -/
  noP0 : Bool := false
  /-- turn the proof-term grading off (`SEMANTEQ_NO_PROOFAUDIT`) -/
  noProofAudit : Bool := false
  /-- turn the antecedent-free replay off (`SEMANTEQ_NO_REPLAY`) -/
  noReplay : Bool := false
  -- the checker's ablation switches
  /-- the reproof re-asserts only the proof's leading `have`/`let` chain, not
  the facts inside case splits and lambdas (`SEMANTEQ_NO_REPLAY_LOCAL_FACTS`) -/
  noReplayLocalFacts : Bool := false
  /-- turn the closed-witness audit off (`SEMANTEQ_NO_WITNESS_CHECK`) -/
  noWitnessCheck : Bool := false
  /-- turn the conjunct-level ablation off (`SEMANTEQ_NO_CONJUNCT_ABLATION`) -/
  noConjunctAblation : Bool := false
  /-- the lambda components of `And.intro`, `Iff.intro` and `Exists.intro` at
  goal role do not count as binding the goal's own objects
  (`SEMANTEQ_NO_CONJUNCT_SURFACE`) -/
  noConjunctSurface : Bool := false
  deriving Inhabited

/-- The configuration as the environment sets it. -/
def Config.fromEnv : IO Config := do
  return {
    depth := ← envNat "DEPTH" 1
    lemmaCap := ← envNat "LEMMA_CAP" 24
    stateCap := ← envNat "STATE_CAP" 24
    discoveryBudget := ← envNat "DISCOVERY_BUDGET" 64
    armBudget := ← envNat "ARM_BUDGET" 80
    deepLevelBudget := ← envNat "DEEP_LEVEL_BUDGET" 1000000
    searchHeartbeats := ← envNat "HEARTBEATS" 100000
    timeoutSecs := ← envNat "TIMEOUT" 20
    maxEnvs := max (← envNat "MAX_ENVS" 4) 1
    strict := ← envSwitch "STRICT"
    trace := ← envSwitch "TRACE"
    auditTrace := ← envSwitch "AUDIT_TRACE"
    noPregate := ← envSwitch "NO_PREGATE"
    noEssential := ← envSwitch "NO_ESSENTIAL"
    noP0 := ← envSwitch "NO_P0"
    noProofAudit := ← envSwitch "NO_PROOFAUDIT"
    noReplay := ← envSwitch "NO_REPLAY"
    noReplayLocalFacts := ← envSwitch "NO_REPLAY_LOCAL_FACTS"
    noWitnessCheck := ← envSwitch "NO_WITNESS_CHECK"
    noConjunctAblation := ← envSwitch "NO_CONJUNCT_ABLATION"
    noConjunctSurface := ← envSwitch "NO_CONJUNCT_SURFACE" }

/-- The configuration in force, set from the environment at start-up and
adjusted by the command-line flags. -/
initialize configRef : IO.Ref Config ← do IO.mkRef (← Config.fromEnv)

/-- The current configuration. -/
def getConfig : BaseIO Config := configRef.get

/-- Command-line overrides (`Main.consumeFlags`). -/
def modifyConfig (f : Config → Config) : IO Unit := configRef.modify f

end SemantEq
