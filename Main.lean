import StaticEval

open StaticEval

/-- `lake exe static_eval <pairs.jsonl> [out.jsonl]` — results stream to stdout as
JSONL while the batch runs (so a killed run keeps everything finished so far) and
are written to `out.jsonl` at the end if given; progress goes to stderr.
Two further modes: `--proof <fixture.lean|dir> ...` runs the ProofChecker over
proof fixtures (`ProofAudit.runProofCli`); `--dump-pack-index <out.json>` writes
the R1 instance-packaging index as inspectable metadata. -/
private def setNat (name : String) (v : String) (act : Nat → IO Unit) : IO Unit := do
  match v.toNat? with
  | some n => act n
  | none => IO.eprintln s!"ignoring non-numeric {name} {v}"

-- Search-strength CLI flags (2026-08-22): --depth, --arm-budget,
-- --discovery-budget, --lemma-cap, --state-cap, --deep-level-budget,
-- --heartbeats — each
-- equivalent to its STATIC_EVAL_* env var (flags win). Consumed from the
-- front of the arg list before mode dispatch.
def consumeFlags : List String → IO (List String)
  | "--depth" :: v :: rest => do
    setNat "--depth" v (StaticEval.depthOverrideRef.set ∘ some); consumeFlags rest
  | "--lemma-cap" :: v :: rest => do
    setNat "--lemma-cap" v (StaticEval.lemmaCapOverrideRef.set ∘ some); consumeFlags rest
  | "--state-cap" :: v :: rest => do
    setNat "--state-cap" v (StaticEval.stateCapOverrideRef.set ∘ some); consumeFlags rest
  | "--arm-budget" :: v :: rest => do
    setNat "--arm-budget" v StaticEval.armBudgetRef.set; consumeFlags rest
  | "--discovery-budget" :: v :: rest => do
    setNat "--discovery-budget" v StaticEval.discoveryBudgetRef.set; consumeFlags rest
  | "--deep-level-budget" :: v :: rest => do
    setNat "--deep-level-budget" v StaticEval.deepLevelBudgetRef.set; consumeFlags rest
  | "--heartbeats" :: v :: rest => do
    setNat "--heartbeats" v StaticEval.searchHeartbeatsRef.set; consumeFlags rest
  | rest => return rest

def main (rawArgs : List String) : IO UInt32 := do
  let args ← consumeFlags rawArgs
  match args with
  | ["--replay", inFile, outFile] =>
    Lean.initSearchPath (← Lean.findSysroot)
    runReplay inFile outFile
  | "--proof" :: paths =>
    Lean.initSearchPath (← Lean.findSysroot)
    ProofAudit.runProofCli paths
  | ["--dump-pack-index", outFile] =>
    -- R1 catalog as inspectable metadata: build the packaging index against
    -- `import Mathlib` and write it as JSON {classHead: [lemmas]}. For
    -- eyeballing and diffing across Mathlib bumps — the runtime always scans
    -- live (~2s/process), so this file is never load-bearing.
    Lean.initSearchPath (← Lean.findSysroot)
    let (env, _) ← cachedImportModules #[`Init, `Mathlib] {}
    let idx ← runMetaM env {} getPackIndex
    let obj := Lean.Json.mkObj <| idx.toList.map fun (h, cs) =>
      (h.toString, Lean.Json.arr (cs.map (Lean.Json.str ·.toString)))
    IO.FS.writeFile outFile (obj.pretty ++ "\n")
    IO.eprintln s!"[static_eval] pack index: {idx.size} class heads -> {outFile}"
    return 0
  | [inFile] | [inFile, _] =>
    Lean.initSearchPath (← Lean.findSysroot)
    let stamp ← metaRecord  -- version + git stamp, first line of stream and out-file
    IO.println stamp.compress
    let results ← runBatch inFile  -- streams each result to stdout as it lands
    if let [_, outFile] := args then
      IO.FS.writeFile outFile
        ("\n".intercalate ((stamp :: results.toList).map (·.compress)) ++ "\n")
    return 0
  | _ =>
    IO.eprintln "usage: static_eval [strength flags] <pairs.jsonl> [out.jsonl] | --proof <fixture.lean|dir>... | --dump-pack-index <out.json>"
    IO.eprintln "  strength flags: --depth N --arm-budget N --discovery-budget N --lemma-cap N --state-cap N --deep-level-budget N --heartbeats N (= STATIC_EVAL_* env vars)"
    return 1
