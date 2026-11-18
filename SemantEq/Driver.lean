import SemantEq.Compile
import SemantEq.Statement
import SemantEq.Context
import SemantEq.Search
import SemantEq.Config

/-!
# Batch driver

Input: JSONL, one pair per line:

  {"id": "...", "reference": "<raw lean source>", "candidate": "<raw lean source>"}

Per pair:

1. both sides are compiled in isolated environments: the gate, and the source
   of per-side error messages and of each side's preamble/statement split;
2. the branched environments are built over the union of the imports; the
   last statement of each side is extracted, side-local definitions are
   unfolded, and the statements are compared type-theoretically;
3. statements past definitional equality get the bidirectional implication
   search: each direction is proved in its own proving environment, which
   holds the antecedent side in full and only the preamble of the target
   side, so the target statement is absent by construction.

Verdicts, in order of the pipeline stage that produces them:

* input:            `MalformedInput` (the line is not valid pair JSON)
* compilation:      `ReferenceCompileError | CandidateCompileError | BothCompileError`
* contexts:         `ContextMergeError` (a side failed to elaborate in the
                    union-import environment; details under `"context"`)
* extraction:       `ReferenceNoStatement | CandidateNoStatement`
* comparison:       `ExactMatch` (alpha-equal after local-definition unfolding)
                    | `DefEq` (definitionally equal)
* implications:     `NotAProposition` (a side's statement is not a `Prop`)
                    | `EquivalentRestricted` (both directions closed by the
                      antecedent-driven search and audited)
                    | `LikelyTooWeak` (only ref → cand closed)
                    | `LikelyTooStrong` (only cand → ref closed)
                    | `Inconclusive` (neither direction closed)
                    | `Timeout` (the pair ran past the wall-clock limit before
                      being accepted)
                    | `InternalError` (invariant violation; see `"errors"`)
-/

namespace SemantEq
open Lean

/-- One input pair, both sides as raw Lean source text. -/
structure PairInput where
  id        : String
  reference : String
  candidate : String

/-- Parse one JSONL line into a pair. -/
def parsePairLine (line : String) : Except String PairInput := do
  let j ← Json.parse line
  let id ← j.getObjValAs? String "id"
  let reference ← j.getObjValAs? String "reference"
  let candidate ← j.getObjValAs? String "candidate"
  return { id, reference, candidate }

/-- The compile-stage verdict; `none` when both sides compile. -/
def compileVerdict? (ref cand : SideReport) : Option String :=
  match ref.ok, cand.ok with
  | true,  true  => none
  | false, true  => some "ReferenceCompileError"
  | true,  false => some "CandidateCompileError"
  | false, false => some "BothCompileError"

/-- The verdict from the two direction outcomes. -/
def implicationVerdict (refToCand candToRef : DirectionOutcome) : String :=
  match refToCand.closed, candToRef.closed with
  | true,  true  => "EquivalentRestricted"
  | true,  false => "LikelyTooWeak"
  | false, true  => "LikelyTooStrong"
  | false, false => "Inconclusive"

/-- The `reference` or `candidate` object of a record: the compile report plus
the extracted statement, when found. -/
def sideJson (r : SideReport) (stmt? : Option ExtractedStatement) : Json :=
  Json.mkObj <|
    [ ("ok", Json.bool r.ok)
    , ("errors", Json.arr (r.errors.map Json.str))
    , ("supersetEnv", Json.bool r.supersetEnv) ]
    ++ match stmt? with
       | some s => [("statement", Json.mkObj
           [ ("name", Json.str s.name.toString)
           , ("type", Json.str s.typePP) ])]
       | none => []

/-- The `context` object of a `ContextMergeError` record. -/
def contextJson (ctx : SharedContext) : Json :=
  Json.mkObj
    [ ("importErrors", Json.arr (ctx.importErrors.map Json.str))
    , ("refErrors", Json.arr (ctx.refErrors.map Json.str))
    , ("candErrors", Json.arr (ctx.candErrors.map Json.str)) ]

/-- Constants used by `e` that are missing from `env`: a sanity check before
proving a goal extracted from a different (but same-base, same-namespace)
environment. -/
def missingConstants (env : Environment) (e : Expr) : Array Name :=
  e.getUsedConstants.filter (fun c => !env.contains c)

/-- Compiler-generated auxiliaries (`_proof_N`) of a statement's own
elaboration exist only in that statement's branch, so the other direction's
goal may reference a constant its proving environment lacks. Each such
internal, Prop-valued constant is added to the direction environment as an
axiom with its type from the shared environment: sound by proof irrelevance,
since nothing computes with its body. Data-valued helpers are not
transplanted (an axiom would be opaque to unfolding) and user-named missing
constants are left alone; both still fail the missing-constants check. -/
def repairMissingAuxes (shared env : Environment) (e : Expr) : IO Environment := do
  let mut env := env
  for c in missingConstants env e do
    if c.isInternalDetail then
      if let some info := shared.find? c then
        -- only Prop-valued constants: an axiom standing in for data would be
        -- opaque to definitional unfolding
        if ← runMetaM shared {} (Meta.isProp info.type) then
          match env.addDeclCore 400000000 (Declaration.axiomDecl
              { name := c, levelParams := info.levelParams,
                type := info.type, isUnsafe := false }) none true with
          | Except.ok env' => env := env'
          | Except.error _ => pure ()
  return env

/-- A direction search under the pair's wall-clock limit: an exception that
arrives after the limit passed is the interrupt, and the direction counts as
not closed; any other exception propagates as before. -/
def underDeadline (tok : IO.CancelToken) (x : IO DirectionOutcome) : IO DirectionOutcome := do
  if ← tok.isSet then return {}
  try x catch e => if ← tok.isSet then return {} else throw e

/-- The environments and statements of a pair once both sides compiled and both
statements were found: what the direction searches (and the replay tool) need. -/
structure PairEnvs where
  /-- proving environment for reference → candidate: the reference statement
  present, the candidate one absent -/
  envA : Environment
  /-- proving environment for candidate → reference -/
  envB : Environment
  /-- comparison environment: both statements, namespaced -/
  env : Environment
  refSrc  : SideSource
  candSrc : SideSource
  /-- the statements as found by the isolated compiles (source positions) -/
  refIso  : ExtractedStatement
  candIso : ExtractedStatement
  /-- the statements in the comparison environment -/
  refStmt  : ExtractedStatement
  candStmt : ExtractedStatement
  cmp : StatementComparison

/-- How far a pair got before the direction searches. Every stage short of
`ready` names the verdict it stands for and carries the payload the record
reports. -/
inductive PairStage
  /-- `ReferenceCompileError` / `CandidateCompileError` / `BothCompileError`,
  or `InternalError` when a compiled side carries no command state -/
  | compileFailed (verdict : String)
  /-- `ContextMergeError`: a header failed to parse, or a side failed to
  elaborate in the union-import environment -/
  | mergeFailed (ctx : SharedContext)
  /-- `ReferenceNoStatement` / `CandidateNoStatement`; the statement that was
  found, if any, still goes into the record -/
  | noStatement (verdict : String) (refStmt? candStmt? : Option ExtractedStatement)
  | ready (envs : PairEnvs)

/-- The two compiled sides and how far the pair got. -/
structure PairPrep where
  ref   : CompiledSide
  cand  : CompiledSide
  stage : PairStage

/-- Compile both sides, build the branched environments, extract and compare
the two statements: everything before the direction searches, shared by the
driver and the replay tool. -/
def preparePair (p : PairInput) : IO PairPrep := do
  let ref ← compileSide p.reference s!"<{p.id}.reference>"
  let cand ← compileSide p.candidate s!"<{p.id}.candidate>"
  let stage ← do
    match compileVerdict? ref.report cand.report, ref.cmdState?, cand.cmdState? with
    | some v, _, _ => pure (PairStage.compileFailed v)
    | none, some refSt, some candSt =>
      let refSrcE ← parseSide p.reference s!"<{p.id}.reference>"
      let candSrcE ← parseSide p.candidate s!"<{p.id}.candidate>"
      match refSrcE, candSrcE with
      | .ok refSrc, .ok candSrc =>
        -- the preamble/statement split positions come from the isolated
        -- compiles; the preambles are elaborated exactly once and every later
        -- environment is an extension
        let refIso? ← lastStatement? refSt.env
        let candIso? ← lastStatement? candSt.env
        match refIso?, candIso? with
        | none, _ => pure (.noStatement "ReferenceNoStatement" none none)
        | _, none => pure (.noStatement "CandidateNoStatement" none none)
        | some refIso, some candIso =>
          let ctx ← buildBranchedContext refSrc candSrc refIso.startPos candIso.startPos
            (candIsoName := candIso.fullName)
          match ctx.envA?, ctx.envB?, ctx.envFull? with
          | some envA, some envB, some env =>
            let refStmt? ← lastStatement? env (ns? := refNamespace)
            let candStmt? ← lastStatement? env (ns? := candNamespace)
            match refStmt?, candStmt? with
            | none, _ => pure (.noStatement "ReferenceNoStatement" refStmt? candStmt?)
            | _, none => pure (.noStatement "CandidateNoStatement" refStmt? candStmt?)
            | some refStmt, some candStmt =>
              let cmp ← compareStatements env refStmt.type candStmt.type
              pure (.ready { envA := envA, envB := envB, env := env,
                             refSrc := refSrc, candSrc := candSrc,
                             refIso := refIso, candIso := candIso,
                             refStmt := refStmt, candStmt := candStmt, cmp := cmp })
          | _, _, _ =>
            pure (.mergeFailed { importErrors := ctx.importErrors,
                                 refErrors := ctx.refErrors, candErrors := ctx.candErrors })
      | .error es, _ | _, .error es => pure (.mergeFailed { importErrors := es })
    | none, _, _ => pure (.compileFailed "InternalError") -- ok sides always carry a command state
  return { ref, cand, stage }

/-- Judge one pair and return its record (the verdicts are listed in the module
doc; `renderPair` is the readable form). -/
def processPair (p : PairInput) : IO Json := do
  let tPair ← IO.monoMsNow
  -- wall-clock limit for the whole pair (`--timeout`, `SEMANTEQ_TIMEOUT`;
  -- 0 = none): a watchdog sets the pair's cancel token when the limit passes;
  -- every `runMetaM` hands the token to Lean's interrupt check, so the search
  -- stops at its next heartbeat check. The verdict is then `Timeout` unless
  -- the pair had already been accepted.
  let limitSecs := (← getConfig).timeoutSecs
  let deadlineTok ← IO.CancelToken.new
  if limitSecs > 0 then
    deadlineTokRef.set (some deadlineTok)
    let _ ← IO.asTask (prio := .dedicated) do
      IO.sleep (limitSecs * 1000).toUInt32
      deadlineTok.set
  else
    deadlineTokRef.set none
  -- the pack memos are keyed by pretty-printed demand types: stable across one
  -- pair's arms, meaningless across pairs
  PackMemo.resetPair
  let prep ← preparePair p
  let mut refStmt? : Option ExtractedStatement := none
  let mut candStmt? : Option ExtractedStatement := none
  let mut cmp? : Option StatementComparison := none
  let mut dirs? : Option (DirectionOutcome × DirectionOutcome) := none
  let mut ctxErr? : Option SharedContext := none
  let mut errors : Array String := #[]
  let mut verdict : String := ""
  match prep.stage with
  | .compileFailed v => verdict := v
  | .mergeFailed ctx =>
    verdict := "ContextMergeError"
    ctxErr? := some ctx
  | .noStatement v r c =>
    verdict := v
    refStmt? := r
    candStmt? := c
  | .ready envs =>
    refStmt? := some envs.refStmt
    candStmt? := some envs.candStmt
    let cmp := envs.cmp
    cmp? := some cmp
    if cmp.alphaEq then
      verdict := "ExactMatch"
    else if cmp.defEq? == some true then
      verdict := "DefEq"
    else if !(← isPropStatement envs.env {} cmp.refExpr)
         || !(← isPropStatement envs.env {} cmp.candExpr) then
      verdict := "NotAProposition"
    else
      -- preamble constants are shared by construction; only a statement's own
      -- auxiliaries can be missing from the other direction's environment
      let envA ← repairMissingAuxes envs.env envs.envA cmp.candExpr
      let envB ← repairMissingAuxes envs.env envs.envB cmp.refExpr
      let missA := missingConstants envA cmp.candExpr
      let missB := missingConstants envB cmp.refExpr
      if !missA.isEmpty || !missB.isEmpty then
        verdict := "InternalError"
        errors := errors.push
          s!"goal constants missing from proving env: {missA ++ missB}"
      else
        -- the forbidden set is the same in both directions, so the discovered
        -- pool is keyed on the statement, not on the role it plays
        let sideNames : NameSet :=
          ({} : NameSet) |>.insert envs.refStmt.fullName |>.insert envs.candStmt.fullName
        -- the two statements' discovery pools are computed at most once per
        -- pair and shared by both directions; the antecedent's canonical form
        -- travels with them, so both roles of a statement are probed alike
        let poolCache ← IO.mkRef
          (none : Option (Array PoolEntry × Array PoolEntry × Array PoolEntry))
        let tRtc ← IO.monoMsNow
        let refToCand ← underDeadline deadlineTok <|
          proveDirectionTiered envA {} cmp.candExpr envs.refStmt.fullName
            sideNames cmp.refExpr (goalIsCand := true) poolCache
        let refToCand := { refToCand with elapsedMs := (← IO.monoMsNow) - tRtc }
        let tCtr ← IO.monoMsNow
        let candToRef ← underDeadline deadlineTok <|
          proveDirectionTiered envB {} cmp.refExpr envs.candStmt.fullName
            sideNames cmp.candExpr (goalIsCand := false) poolCache
        let candToRef := { candToRef with elapsedMs := (← IO.monoMsNow) - tCtr }
        dirs? := some (refToCand, candToRef)
        verdict := implicationVerdict refToCand candToRef
  -- the limit passed and the pair was not accepted: whatever stopped is reported
  -- as the time limit, not as a judgement
  if limitSecs > 0 && (← deadlineTok.isSet)
      && !(["ExactMatch", "DefEq", "EquivalentRestricted"].contains verdict) then
    verdict := "Timeout"
  deadlineTokRef.set none
  return Json.mkObj <|
    [ ("id", Json.str p.id)
    , ("verdict", Json.str verdict)
    , ("elapsedMs", Lean.ToJson.toJson ((← IO.monoMsNow) - tPair))
    , ("reference", sideJson prep.ref.report refStmt?)
    , ("candidate", sideJson prep.cand.report candStmt?) ]
    ++ (match cmp? with | some cmp => [("comparison", toJson cmp)] | none => [])
    ++ (match dirs? with
        | some (rtc, ctr) => [("directions", Json.mkObj
            [("ref_to_cand", toJson rtc), ("cand_to_ref", toJson ctr)])]
        | none => [])
    ++ (match ctxErr? with | some c => [("context", contextJson c)] | none => [])
    ++ (if errors.isEmpty then [] else [("errors", Json.arr (errors.map Json.str))])

/-- `processPair` behind the last-resort barrier: one pathological pair must
never kill a batch, so an uncaught exception becomes an `InternalError` record. -/
def guardedPair (p : PairInput) : IO Json := do
  try
    processPair p
  catch e =>
    pure <| Json.mkObj
      [ ("id", Json.str p.id)
      , ("verdict", Json.str "InternalError")
      , ("errors", Json.arr #[Json.str s!"uncaught exception: {e}"]) ]
def malformedResult (lineNo : Nat) (err : String) : Json :=
  Json.mkObj
    [ ("id", Json.str s!"<line {lineNo}>")
    , ("verdict", Json.str "MalformedInput")
    , ("error", Json.str err) ]

/-- Current resident set size in MB, read from `/proc/self/status` (Linux only). -/
def rssMB : IO (Option Nat) := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    for line in status.splitOn "\n" do
      if line.startsWith "VmRSS" then
        if let some kb := (String.ofList (line.toList.filter (·.isDigit))).toNat? then
          return some (kb / 1024)
    return none
  catch _ =>
    return none

/-- Pre-import the batch's most frequent import set before processing starts.
With the subset-collapsing cache this makes the dominant environment
(typically `import Mathlib`) the first one built, so narrow-import sides that
come earlier in file order are served from it instead of triggering their own
imports. The scan only parses headers; it builds no environment. -/
def warmUpCache (pairs : Array PairInput) (opts : Options := {}) : IO Unit := do
  let mut counts : Array ((Array Name) × Nat × Array Import) := #[]
  for p in pairs do
    for src in [p.reference, p.candidate] do
      if let .ok side ← parseSide src "<warmup>" then
        let key := (side.imports.map (·.module)).qsort (·.toString < ·.toString)
        match counts.findIdx? (·.1 == key) with
        | some i => counts := counts.modify i fun (k, n, imps) => (k, n + 1, imps)
        | none   => counts := counts.push (key, 1, side.imports)
  let some (key, _, imports) :=
      counts.foldl (init := none) fun best entry =>
        match best with
        | some (_, bn, _) => if entry.2.1 > bn then some entry else best
        | none => some entry
    | return ()
  IO.eprintln s!"[semanteq] warm-up: importing the batch's most frequent set {key}"
  try
    discard <| cachedImportModules imports opts
  catch e =>
    IO.eprintln s!"[semanteq] warm-up import failed (continuing): {e}"

/-- Human-readable rendering of one pair record (the default stdout format;
`--raw` prints the JSON record instead): the verdict, then for each direction
the proof that closed it, or `null` when the direction did not close. -/
def renderPair (j : Json) : String := Id.run do
  let str (o : Json) (k : String) : String := (o.getObjValAs? String k).toOption.getD ""
  let mut out := s!"── {str j "id"}\n   verdict: {str j "verdict"}"
  if let .ok ms := j.getObjValAs? Nat "elapsedMs" then out := out ++ s!"   ({ms} ms)"
  out := out ++ "\n"
  for side in ["reference", "candidate"] do
    if let .ok sj := j.getObjVal? side then
      if let .ok errs := sj.getObjValAs? (Array String) "errors" then
        if !errs.isEmpty then
          out := out ++ s!"   {side} errors:\n"
          for e in errs do out := out ++ s!"      {e}\n"
  if let .ok errs := j.getObjValAs? (Array String) "errors" then
    for e in errs do out := out ++ s!"   error: {e}\n"
  if let .ok e := j.getObjValAs? String "error" then out := out ++ s!"   error: {e}\n"
  let indent (s : String) : String := String.intercalate "\n              " (s.splitOn "\n")
  match j.getObjVal? "directions" with
  | .ok dirs =>
    for (k, label) in [("ref_to_cand", "ref ⇒ cand"), ("cand_to_ref", "cand ⇒ ref")] do
      if let .ok d := dirs.getObjVal? k then
        if (d.getObjValAs? Bool "closed").toOption.getD false then
          out := out ++ s!"   {label}: proved\n      script: {str d "script"}\n      proof:  {indent (str d "proof")}\n"
        else
          -- one line on why: the last audit refusal when a proof was found and
          -- refused, otherwise how many attempts produced no proof, or the limit
          let arr (k : String) : Array String := (d.getObjValAs? (Array String) k).toOption.getD #[]
          let rejected := arr "rejectedScripts"
          let failed := arr "failedScripts"
          let ms := (d.getObjValAs? Nat "elapsedMs").toOption.getD 0
          let timedOut := str j "verdict" == "Timeout"
          let why :=
            if let some r := rejected.back? then
              s!"last refusal ({rejected.size} proof{if rejected.size == 1 then "" else "s"} refused): {takeChars r 220}"
            else if timedOut && ms == 0 then "not attempted, the time limit had passed"
            else if timedOut then s!"stopped by the time limit after {failed.size} attempts without a proof"
            else if failed.isEmpty then "no attempt produced a proof"
            else s!"no proof found in {failed.size} attempts"
          out := out ++ s!"   {label}: not proved\n      {why}\n"
  | .error _ =>
    let v := str j "verdict"
    if v == "ExactMatch" || v == "DefEq" then
      out := out ++ "   identical statements, no implication proof needed\n"
  return out

/-- Human-readable rendering of the `_meta` stamp. -/
def renderMeta (stamp : Json) : String :=
  match stamp.getObjVal? "_meta" with
  | .ok m =>
    let g (k : String) : String := (m.getObjValAs? String k).toOption.getD "?"
    let dirty := (m.getObjValAs? Bool "dirty").toOption.getD false
    s!"{g "tool"} {g "version"}  git {g "git"}{if dirty then " (dirty)" else ""}  {g "date"}"
  | .error _ => stamp.compress

/-- Process a JSONL file of pairs; returns one JSON result per pair. Each result is
also handed to `emit` as soon as it is produced (the CLI prints it readable or raw),
so a crashed or killed run keeps everything finished so far. -/
def runBatch (inFile : System.FilePath) (emit : Json → IO Unit) : IO (Array Json) := do
  let trace := (← getConfig).trace
  let lines ← IO.FS.lines inFile
  let mut parsed : Array (Nat × Except String PairInput) := #[]
  let mut lineNo := 0
  for line in lines do
    lineNo := lineNo + 1
    unless line.trimAscii.isEmpty do
      parsed := parsed.push (lineNo, parsePairLine line)
  warmUpCache (parsed.filterMap fun (_, r) => r.toOption)
  let mut results := #[]
  for (ln, r) in parsed do
    let result ← match r with
      | .error e => pure (malformedResult ln e)
      | .ok p => do
        let mem := match ← rssMB with
          | some mb => if trace then s!" (rss {mb} MB)" else ""
          | none => ""
        IO.eprintln s!"[semanteq] processing {p.id}{mem}"
        guardedPair p
    emit result
    results := results.push result
  return results
end SemantEq
