import SemantEq

open SemantEq

/-- `lake exe semanteq <pairs.jsonl> [out.jsonl]` — results stream to stdout as
they land, in a readable form by default or as JSONL with `--raw` (so a killed
run keeps everything finished so far), and the JSONL records are written to
`out.jsonl` at the end if given; progress goes to stderr.
`lake exe semanteq <ref.lean> <cand.lean>` — exactly two `.lean` files and no
JSONL: the two sources are read and judged as ONE pair through the same
pipeline as a JSONL row (id = `<ref stem>__vs__<cand stem>`), result to stdout.
Two further modes: `--proof <fixture.lean|dir> ...` runs the ProofChecker over
proof fixtures (`ProofAudit.runProofCli`); `--dump-pack-index <out.json>` writes
the instance-packaging index as inspectable metadata. -/
private def setNat (name : String) (v : String) (act : Nat → IO Unit) : IO Unit := do
  match v.toNat? with
  | some n => act n
  | none => IO.eprintln s!"ignoring non-numeric {name} {v}"

-- Search-strength CLI flags: --depth, --arm-budget,
-- --discovery-budget, --lemma-cap, --state-cap, --deep-level-budget,
-- --heartbeats — each
-- equivalent to its SEMANTEQ_* env var (flags win). Consumed from the
-- front of the arg list before mode dispatch.
initialize rawOutputRef : IO.Ref Bool ← IO.mkRef false
/-- `--strict`: the strict reading of the definition as a mode. A
severe use (a library fact meeting a hypothesis of the antecedent while drawing
on nothing local) fails the proof instead of being recorded, at the top level
and inside the proofs of antecedent-free local bridges (`have h : A ↔ B := …`,
bridge-shaped in-file lemmas), which are read in both modes. Off by default. -/
initialize strictProofRef : IO.Ref Bool ← IO.mkRef false

def consumeFlags : List String → IO (List String)
  | "--raw" :: rest => do
    rawOutputRef.set true; consumeFlags rest
  | "--strict" :: rest => do
    strictProofRef.set true; consumeFlags rest
  | "--depth" :: v :: rest => do
    setNat "--depth" v (SemantEq.depthOverrideRef.set ∘ some); consumeFlags rest
  | "--lemma-cap" :: v :: rest => do
    setNat "--lemma-cap" v (SemantEq.lemmaCapOverrideRef.set ∘ some); consumeFlags rest
  | "--state-cap" :: v :: rest => do
    setNat "--state-cap" v (SemantEq.stateCapOverrideRef.set ∘ some); consumeFlags rest
  | "--arm-budget" :: v :: rest => do
    setNat "--arm-budget" v SemantEq.armBudgetRef.set; consumeFlags rest
  | "--discovery-budget" :: v :: rest => do
    setNat "--discovery-budget" v SemantEq.discoveryBudgetRef.set; consumeFlags rest
  | "--deep-level-budget" :: v :: rest => do
    setNat "--deep-level-budget" v SemantEq.deepLevelBudgetRef.set; consumeFlags rest
  | "--heartbeats" :: v :: rest => do
    setNat "--heartbeats" v SemantEq.searchHeartbeatsRef.set; consumeFlags rest
  | rest => return rest

/-- Print one record to stdout, readable by default or raw JSON under `--raw`. -/
def emitPair (j : Lean.Json) : IO Unit := do
  if ← rawOutputRef.get then IO.println j.compress else IO.print (renderPair j)
  (← IO.getStdout).flush

def emitMeta (stamp : Lean.Json) : IO Unit := do
  if ← rawOutputRef.get then IO.println stamp.compress else IO.println (renderMeta stamp)

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

/-- Two-file mode: `<ref.lean> <cand.lean>`. The two files are read
verbatim and judged as one pair exactly as a JSONL row would be (same
`processPair`, same warm-up); the result is streamed to stdout after the
`_meta` stamp. -/
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
  -- same last-resort barrier as `runBatch`: an exception becomes a record
  let onErr (e : IO.Error) : Lean.Json := Lean.Json.mkObj
    [ ("id", Lean.Json.str p.id)
    , ("verdict", Lean.Json.str "InternalError")
    , ("errors", Lean.Json.arr #[Lean.Json.str s!"uncaught exception: {e}"]) ]
  let result ← try processPair p catch e => pure (onErr e)
  emitPair result
  return 0

def main (rawArgs : List String) : IO UInt32 := do
  let args ← consumeFlags rawArgs
  if (← IO.getEnv "SEMANTEQ_STRICT").any (fun v => v != "" && v != "0") then strictProofRef.set true
  match args with
  | ["--replay", inFile, outFile] =>
    Lean.initSearchPath (← Lean.findSysroot)
    runReplay inFile outFile
  | "--proof" :: paths =>
    Lean.initSearchPath (← Lean.findSysroot)
    ProofAudit.runProofCli paths (raw := ← rawOutputRef.get) (strict := ← strictProofRef.get)
  | ["--dump-pack-index", outFile] =>
    -- catalog as inspectable metadata: build the packaging index against
    -- `import Mathlib` and write it as JSON {classHead: [lemmas]}. For
    -- eyeballing and diffing across Mathlib bumps — the runtime always scans
    -- live (~2s/process), so this file is never load-bearing.
    Lean.initSearchPath (← Lean.findSysroot)
    let (env, _) ← cachedImportModules #[`Init, `Mathlib] {}
    let idx ← runMetaM env {} getPackIndex
    let obj := Lean.Json.mkObj <| idx.toList.map fun (h, cs) =>
      (h.toString, Lean.Json.arr (cs.map (Lean.Json.str ·.toString)))
    IO.FS.writeFile outFile (obj.pretty ++ "\n")
    IO.eprintln s!"[semanteq] pack index: {idx.size} class heads -> {outFile}"
    return 0
  | [refFile, candFile] =>
    if refFile.endsWith ".lean" && candFile.endsWith ".lean" then
      runTwoFiles refFile candFile
    else
      runJsonl refFile (some candFile)
  | [inFile] => runJsonl inFile none
  | _ =>
    IO.eprintln "usage: semanteq [--raw] [strength flags] <pairs.jsonl> [out.jsonl] | <ref.lean> <cand.lean> | [--strict] --proof <fixture.lean|dir>... | --dump-pack-index <out.json>"
    IO.eprintln "  --raw: print JSON records on stdout instead of the readable summary (the out-file is always JSONL)"
    IO.eprintln "  --strict: the strict reading — a severe use (library fact meeting an antecedent hypothesis from nothing local) fails, at the top level and inside local bridge proofs (= SEMANTEQ_STRICT=1)"
    IO.eprintln "  strength flags: --depth N --arm-budget N --discovery-budget N --lemma-cap N --state-cap N --deep-level-budget N --heartbeats N (= SEMANTEQ_* env vars)"
    return 1
