import SemantEq
open SemantEq

/-!
# Command line

`lake exe semanteq <pairs.jsonl> [out.jsonl]` judges every pair of a JSONL
file. Results stream to stdout as they finish, readable by default or as JSON
records with `--raw`, so an interrupted run keeps everything finished so far;
the JSON records are also written to `out.jsonl` when given. Progress goes to
stderr.

`lake exe semanteq <ref.lean> <cand.lean>` judges two Lean files as one pair
through the same pipeline (id `<ref stem>__vs__<cand stem>`).

`lake exe semanteq --proof <fixture.lean|dir> ...` runs the proof checker
over fixtures (`ProofAudit.runProofCli`).
-/

/-- Apply a numeric flag value; a value that is not a number is ignored with a
message. -/
private def setNat (name : String) (v : String) (act : Nat → IO Unit) : IO Unit := do
  match v.toNat? with
  | some n => act n
  | none => IO.eprintln s!"ignoring non-numeric {name} {v}"

/-- Command-line flags, consumed from the front of the argument list before
mode dispatch; each overrides the corresponding `SEMANTEQ_*` variable
(`Config.fromEnv`). -/
def consumeFlags : List String → IO (List String)
  | "--raw" :: rest => do
    modifyConfig (fun c => { c with raw := true }); consumeFlags rest
  | "--strict" :: rest => do
    modifyConfig (fun c => { c with strict := true }); consumeFlags rest
  | "--depth" :: v :: rest => do
    setNat "--depth" v (fun n => modifyConfig fun c => { c with depth := n }); consumeFlags rest
  | "--lemma-cap" :: v :: rest => do
    setNat "--lemma-cap" v (fun n => modifyConfig fun c => { c with lemmaCap := n }); consumeFlags rest
  | "--state-cap" :: v :: rest => do
    setNat "--state-cap" v (fun n => modifyConfig fun c => { c with stateCap := n }); consumeFlags rest
  | "--arm-budget" :: v :: rest => do
    setNat "--arm-budget" v (fun n => modifyConfig fun c => { c with armBudget := n }); consumeFlags rest
  | "--discovery-budget" :: v :: rest => do
    setNat "--discovery-budget" v (fun n => modifyConfig fun c => { c with discoveryBudget := n }); consumeFlags rest
  | "--deep-level-budget" :: v :: rest => do
    setNat "--deep-level-budget" v (fun n => modifyConfig fun c => { c with deepLevelBudget := n }); consumeFlags rest
  | "--heartbeats" :: v :: rest => do
    setNat "--heartbeats" v (fun n => modifyConfig fun c => { c with searchHeartbeats := n }); consumeFlags rest
  | "--timeout" :: v :: rest => do
    setNat "--timeout" v (fun n => modifyConfig fun c => { c with timeoutSecs := n }); consumeFlags rest
  | rest => return rest

/-- Print one record to stdout, readable by default or raw JSON under `--raw`. -/
def emitPair (j : Lean.Json) : IO Unit := do
  if (← getConfig).raw then IO.println j.compress else IO.print (renderPair j)
  (← IO.getStdout).flush
def emitMeta (stamp : Lean.Json) : IO Unit := do
  if (← getConfig).raw then IO.println stamp.compress else IO.println (renderMeta stamp)

/-- JSONL batch mode: `<pairs.jsonl> [out.jsonl]`. -/
def runJsonl (inFile : String) (outFile? : Option String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let stamp ← metaRecord  -- version + git stamp, first line of stream and out-file
  emitMeta stamp
  let results ← runBatch inFile emitPair  -- streams each result to stdout as it lands
  if let some outFile := outFile? then
    IO.FS.writeFile outFile
      ("\n".intercalate ((stamp :: results.toList).map (·.compress)) ++ "\n")
  return 0

/-- Two-file mode: `<ref.lean> <cand.lean>`. The two files are read verbatim
and judged as one pair exactly as a JSONL row would be (same `processPair`,
same warm-up); the result follows the `_meta` stamp on stdout. -/
def runTwoFiles (refFile candFile : String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let stem (f : String) : String := (System.FilePath.mk f).fileStem.getD f
  let p : PairInput :=
    { id := s!"{stem refFile}__vs__{stem candFile}"
      reference := ← IO.FS.readFile refFile
      candidate := ← IO.FS.readFile candFile }
  let stamp ← metaRecord
  emitMeta stamp
  warmUpCache #[p]
  IO.eprintln s!"[semanteq] processing {p.id}"
  let result ← guardedPair p
  emitPair result
  return 0
def main (rawArgs : List String) : IO UInt32 := do
  let args ← consumeFlags rawArgs
  match args with
  | "--proof" :: paths =>
    Lean.initSearchPath (← Lean.findSysroot)
    ProofAudit.runProofCli paths (raw := (← getConfig).raw) (strict := (← getConfig).strict)
  | [refFile, candFile] =>
    if refFile.endsWith ".lean" && candFile.endsWith ".lean" then
      runTwoFiles refFile candFile
    else
      runJsonl refFile (some candFile)
  | [inFile] => runJsonl inFile none
  | _ =>
    IO.eprintln "usage: semanteq [--raw] [--timeout N] [strength flags] <pairs.jsonl> [out.jsonl] | <ref.lean> <cand.lean> | [--strict] --proof <fixture.lean|dir>..."
    IO.eprintln "  --raw: print JSON records on stdout instead of the readable summary (the out-file is always JSONL)"
    IO.eprintln "  --timeout N: wall-clock limit per pair in seconds for the evaluator, default 20; a pair over the limit reports Timeout; 0 disables (= SEMANTEQ_TIMEOUT)"
    IO.eprintln "  --strict: the strict reading — a severe use (library fact meeting an antecedent hypothesis from nothing local) fails, at the top level and inside local bridge proofs (= SEMANTEQ_STRICT=1)"
    IO.eprintln "  strength flags: --depth N --arm-budget N --discovery-budget N --lemma-cap N --state-cap N --deep-level-budget N --heartbeats N (= SEMANTEQ_* env vars)"
    return 1
