import StaticEval.Compile
import StaticEval.Statement
import StaticEval.Context
import StaticEval.Search

/-!
# Batch driver (Milestones 1–3.6)

Input: JSONL, one pair per line:

  {"id": "...", "reference": "<raw lean source>", "candidate": "<raw lean source>"}

Per pair:

1. both sides are compiled in isolated environments (M1) — the gate, and the source of
   per-side error messages and of each side's preamble/statement split point;
2. one comparison environment is built from the union of their imports with each
   side's full body namespaced (M2.5); the last open statement of each side is
   extracted, side-local definitions are unfolded, and the statements are compared
   type-theoretically (M2);
3. statements past definitional equality get the bidirectional implication search
   (M3/3.6): each direction is proved in its own proving environment, containing the
   antecedent side in full (its statement a genuine named theorem) and only the
   *preamble* of the target side — the target statement is absent by construction.

Verdicts, in order of the pipeline stage that produced them:

* input:            `MalformedInput` (line is not valid pair JSON)
* M1 (compilation): `ReferenceCompileError | CandidateCompileError | BothCompileError`
* M2.5 (contexts):  `ContextMergeError` (a side failed to elaborate in a union-import
                    environment; details under `"context"`)
* M2 (extraction):  `ReferenceNoStatement | CandidateNoStatement`
* M2 (comparison):  `ExactMatch` (alpha-equal after local-def unfolding)
                    | `DefEq` (definitionally equal)
* M3.6 (implications):
                    `NotAProposition` (a side's statement is not a `Prop`)
                    | `EquivalentRestricted` (both directions closed by the
                      antecedent-driven strict ladder)
                    | `EquivalentUnrestricted` (a direction needed the diagnostic
                      closers — decision procedures / library search; BEq-grade)
                    | `LikelyTooWeak` (only ref → cand closed)
                    | `LikelyTooStrong` (only cand → ref closed)
                    | `Inconclusive` (neither direction closed)
                    | `InternalError` (invariant violation; see `"errors"`)
-/

namespace StaticEval

open Lean

/-- One input pair, both sides as raw Lean source text. -/
structure PairInput where
  id        : String
  reference : String
  candidate : String

def parsePairLine (line : String) : Except String PairInput := do
  let j ← Json.parse line
  let id ← j.getObjValAs? String "id"
  let reference ← j.getObjValAs? String "reference"
  let candidate ← j.getObjValAs? String "candidate"
  return { id, reference, candidate }

def compileVerdict? (ref cand : SideReport) : Option String :=
  match ref.ok, cand.ok with
  | true,  true  => none
  | false, true  => some "ReferenceCompileError"
  | true,  false => some "CandidateCompileError"
  | false, false => some "BothCompileError"

def implicationVerdict (refToCand candToRef : DirectionOutcome) : String :=
  match refToCand.closed, candToRef.closed with
  | true,  true  => "EquivalentRestricted"  -- only the strict tier closes (v1.0.0)
  | true,  false => "LikelyTooWeak"
  | false, true  => "LikelyTooStrong"
  | false, false => "Inconclusive"

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

def contextJson (ctx : SharedContext) : Json :=
  Json.mkObj
    [ ("importErrors", Json.arr (ctx.importErrors.map Json.str))
    , ("refErrors", Json.arr (ctx.refErrors.map Json.str))
    , ("candErrors", Json.arr (ctx.candErrors.map Json.str)) ]

/-- Constants used by `e` that are missing from `env` — a sanity check before proving
a goal extracted from a different (but same-base, same-namespace) environment. -/
def missingConstants (env : Environment) (e : Expr) : Array Name :=
  e.getUsedConstants.filter (fun c => !env.contains c)

/-- **M4.8 Fix 0.** Def elaboration mints `_proof_N`-style internal auxiliaries
that carry NO value even in the kernel env (measured: opaque in both envs), so
they can be neither δ-expanded out of the canonical statement expr nor assumed
to re-elaborate under the same names in the per-direction envs. Repair: add each
missing INTERNAL-DETAIL constant to the direction env as an AXIOM with its type
from the shared env — sound, because it is an honest theorem of the shared
elaboration; only its name/type are needed for the goal expr to typecheck, its
value is never evaluated. User-named missing constants still error (a real bug
signal, not repairable noise). -/
def repairMissingAuxes (shared env : Environment) (e : Expr) : IO Environment := do
  let mut env := env
  for c in missingConstants env e do
    if c.isInternalDetail then
      if let some info := shared.find? c then
        -- HARDENING (Henry, 2026-08-03): transplant ONLY Prop-valued constants.
        -- The justification is proof irrelevance — an axiom can stand in for a
        -- proof because nothing computes with its body. A DATA-valued helper
        -- (e.g. a compiler-outlined `match_N` function) transplanted as an axiom
        -- would typecheck but become silently OPAQUE to definitional unfolding.
        -- Non-Prop stays missing, so the missing-constants check errors loudly.
        if ← runMetaM shared {} (Meta.isProp info.type) then
          match env.addDeclCore 400000000 (Declaration.axiomDecl
              { name := c, levelParams := info.levelParams,
                type := info.type, isUnsafe := false }) none true with
          | Except.ok env' => env := env'
          | Except.error _ => pure ()
  return env

def processPair (p : PairInput) : IO Json := do
  let tPair ← IO.monoMsNow
  -- R1(b): the pack memos are keyed by pp'd demand types — stable across one
  -- pair's arms, meaningless across pairs. Clear per pair.
  packFailCache.set []
  packRecipeCache.set []
  satRuleCache.set []
  ematchBridgesRef.set #[]
  ematchAnteRef.set none
  ematchThmFails.set 0
  ematchCase2Drops.set 0
  let ref ← compileSide p.reference s!"<{p.id}.reference>"
  let cand ← compileSide p.candidate s!"<{p.id}.candidate>"
  let mut refStmt? : Option ExtractedStatement := none
  let mut candStmt? : Option ExtractedStatement := none
  let mut cmp? : Option StatementComparison := none
  let mut dirs? : Option (DirectionOutcome × DirectionOutcome) := none
  let mut ctxErr? : Option SharedContext := none
  let mut errors : Array String := #[]
  let mut verdict : String := ""
  match compileVerdict? ref.report cand.report, ref.cmdState?, cand.cmdState? with
  | some v, _, _ => verdict := v
  | none, some refSt, some candSt =>
    let refSrcE ← parseSide p.reference s!"<{p.id}.reference>"
    let candSrcE ← parseSide p.candidate s!"<{p.id}.candidate>"
    match refSrcE, candSrcE with
    | .ok refSrc, .ok candSrc =>
      -- M4.9-branch-env: the preamble/statement split positions come from the
      -- isolated compiles and are needed UP FRONT now — the preambles are
      -- elaborated exactly once (env₀) and every later env is an extension.
      let refIso? ← lastStatement? refSt.env
      let candIso? ← lastStatement? candSt.env
      match refIso?, candIso? with
      | none, _ => verdict := "ReferenceNoStatement"
      | _, none => verdict := "CandidateNoStatement"
      | some refIso, some candIso =>
      let ctx ← buildBranchedContext refSrc candSrc refIso.startPos candIso.startPos
        (candIsoName := candIso.fullName)
      match ctx.envA?, ctx.envB?, ctx.envFull? with
      | _, _, none | _, none, _ | none, _, _ =>
        verdict := "ContextMergeError"
        ctxErr? := some { importErrors := ctx.importErrors,
                          refErrors := ctx.refErrors, candErrors := ctx.candErrors }
      | some envA, some envB, some env =>
        refStmt? ← lastStatement? env (ns? := refNamespace)
        candStmt? ← lastStatement? env (ns? := candNamespace)
        match refStmt?, candStmt? with
        | none, _ => verdict := "ReferenceNoStatement"
        | _, none => verdict := "CandidateNoStatement"
        | some refStmt, some candStmt =>
          let cmp ← compareStatements env refStmt.type candStmt.type
          cmp? := some cmp
          if cmp.alphaEq then
            verdict := "ExactMatch"
          else if cmp.defEq? == some true then
            verdict := "DefEq"
          else if !(← isPropStatement env {} cmp.refExpr)
               || !(← isPropStatement env {} cmp.candExpr) then
            verdict := "NotAProposition"
          else
            -- M4.9-branch-env: envA/envB are extensions of env₀ — preamble
            -- constants (incl. `_proof_N` auxes) are shared by construction.
            -- Fix 0's transplant survives only for statement-level auxiliaries.
            do
                let envA ← repairMissingAuxes env envA cmp.candExpr
                let envB ← repairMissingAuxes env envB cmp.refExpr
                let missA := missingConstants envA cmp.candExpr
                let missB := missingConstants envB cmp.refExpr
                if !missA.isEmpty || !missB.isEmpty then
                  verdict := "InternalError"
                  errors := errors.push
                    s!"goal constants missing from proving env: {missA ++ missB}"
                else
                  -- M4.7-S3c: ROLE-INDEPENDENT forbidden set — the union of both
                  -- sides' statement constants, identical in both directions. A
                  -- no-op today (the target side is elaborated preamble-only, so
                  -- its constant is absent from that direction's env), but it lets
                  -- the discovered pool be keyed on the STATEMENT rather than on
                  -- the role the statement is currently playing.
                  let sideNames : NameSet :=
                    ({} : NameSet) |>.insert refStmt.fullName |>.insert candStmt.fullName
                  -- M4.7-S3d: the ante's CANONICAL Expr travels with it, so both
                  -- roles of a statement are probed on the same form (goal role
                  -- already used these; the ante role used the raw decl type).
                  -- M4.7-S6: the two statements' discovery pools are computed at
                  -- most once per PAIR (lazily, by whichever direction first needs
                  -- phase 2) and shared across both directions via this cache.
                  let poolCache ← IO.mkRef
                    (none : Option (Array PoolEntry × Array PoolEntry × Array PoolEntry))
                  let tRtc ← IO.monoMsNow
                  let refToCand ← proveDirectionTiered envA {} cmp.candExpr refStmt.fullName
                    sideNames cmp.refExpr (goalIsCand := true) poolCache
                  let refToCand := { refToCand with elapsedMs := (← IO.monoMsNow) - tRtc }
                  let tCtr ← IO.monoMsNow
                  let candToRef ← proveDirectionTiered envB {} cmp.refExpr candStmt.fullName
                    sideNames cmp.candExpr (goalIsCand := false) poolCache
                  let candToRef := { candToRef with elapsedMs := (← IO.monoMsNow) - tCtr }
                  dirs? := some (refToCand, candToRef)
                  verdict := implicationVerdict refToCand candToRef

    | .error es, _ =>
      verdict := "ContextMergeError"
      ctxErr? := some { importErrors := es }
    | _, .error es =>
      verdict := "ContextMergeError"
      ctxErr? := some { importErrors := es }
  | none, _, _ => verdict := "InternalError" -- ok sides always carry a command state
  let c2 ← ematchCase2Drops.get
  if c2 > 0 then
    IO.eprintln s!"[static_eval] R3 case-2 drops on {p.id}: {c2}"
  let tf ← ematchThmFails.get
  if tf > 0 then
    IO.eprintln s!"[static_eval] R3 thm-registration failures on {p.id}: {tf}"
  return Json.mkObj <|
    [ ("id", Json.str p.id)
    , ("verdict", Json.str verdict)
    , ("elapsedMs", Lean.ToJson.toJson ((← IO.monoMsNow) - tPair))
    , ("reference", sideJson ref.report refStmt?)
    , ("candidate", sideJson cand.report candStmt?) ]
    ++ (match cmp? with | some cmp => [("comparison", toJson cmp)] | none => [])
    ++ (match dirs? with
        | some (rtc, ctr) => [("directions", Json.mkObj
            [("ref_to_cand", toJson rtc), ("cand_to_ref", toJson ctr)])]
        | none => [])
    ++ (match ctxErr? with | some c => [("context", contextJson c)] | none => [])
    ++ (if errors.isEmpty then [] else [("errors", Json.arr (errors.map Json.str))])

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

/-- Pre-import the batch's most frequent import set before processing starts. With
the subset-collapsing cache, this makes the dominant environment (typically
`import Mathlib`) the FIRST one built, so narrow-import sides processed earlier in
file order are served from it instead of triggering their own imports. Header
parsing only — no environments are built for the scan itself. -/
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
  IO.eprintln s!"[static_eval] warm-up: importing the batch's most frequent set {key}"
  try
    discard <| cachedImportModules imports opts
  catch e =>
    IO.eprintln s!"[static_eval] warm-up import failed (continuing): {e}"

/-- Process a JSONL file of pairs; returns one JSON result per pair. Each result is
also streamed to stdout as soon as it is produced, so a crashed or killed run keeps
everything finished so far. -/
def runBatch (inFile : System.FilePath) : IO (Array Json) := do
  let trace := (← IO.getEnv "STATIC_EVAL_TRACE").isSome
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
        IO.eprintln s!"[static_eval] processing {p.id}{mem}"
        -- last-resort barrier: one pathological pair must never kill the batch
        try
          processPair p
        catch e =>
          pure <| Json.mkObj
            [ ("id", Json.str p.id)
            , ("verdict", Json.str "InternalError")
            , ("errors", Json.arr #[Json.str s!"uncaught exception: {e}"]) ]
    IO.println result.compress
    (← IO.getStdout).flush
    results := results.push result
  return results

end StaticEval
