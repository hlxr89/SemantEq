import Lean
import SemantEq.Config
import SemantEq.Logic
import SemantEq.Compile
import SemantEq.Statement
import SemantEq.Search
import SemantEq.ProofAudit.Walk
import SemantEq.ProofAudit.Reproof

/-!
# Fixtures and the `--proof` command

A fixture file names the assumed statement(s) as `sorry`-proved theorems and
the goal with a real proof; `auditFixture` runs the walk, the axiom
accounting and the reproof, and renders the verdict.
-/

namespace SemantEq
namespace ProofAudit
open Lean Elab Meta

/-- The verdict record of one fixture: `verdict` is `PASS`, `FAIL`,
`SKIP_SORRY` or `ERROR`; `flags` holds the warnings (`severe: …` for the
severe tier, `axiom …` for an axiom beyond the standard ones); `reasons` the
failure reasons; then the antecedent, goal and assumed theorem names. -/
structure FixtureResult where
  file    : String
  verdict : String
  flags   : Array String := #[]
  reasons : Array String := #[]
  ante    : Name := .anonymous
  goal    : Name := .anonymous
  assumed : Array Name := #[]

/-- The JSON record: `flags` is the warning count, `flagDetails` the list. -/
def FixtureResult.toJson (r : FixtureResult) : Json :=
  Json.mkObj
    [ ("file", Json.str r.file)
    , ("verdict", Json.str r.verdict)
    , ("flags", Lean.ToJson.toJson r.flags.size)
    , ("flagDetails", Json.arr (r.flags.map Json.str))
    , ("reasons", Json.arr (r.reasons.map Json.str))
    , ("ante", Json.str r.ante.toString)
    , ("goal", Json.str r.goal.toString)
    , ("assumed", Json.arr (r.assumed.map (Json.str ·.toString))) ]

/-- Human-readable rendering of a fixture verdict (the default stdout format;
`--raw` prints the JSON record instead): the verdict, the reasons of a
`FAIL`, then the warnings, the ordinary tolerated uses as counts by kind,
every severe warning in full, and any axiom beyond the three standard
ones. -/
def FixtureResult.render (r : FixtureResult) : String := Id.run do
  let mut out := s!"── {r.file}\n   verdict: {r.verdict}"
  if r.ante != .anonymous then out := out ++ s!"   (antecedent {r.ante}, goal {r.goal})"
  out := out ++ "\n"
  if r.verdict != "PASS" then
    if r.reasons.isEmpty then
      if r.verdict == "FAIL" then out := out ++ "   reasons: none recorded\n"
    else
      out := out ++ "   reasons:\n"
      for x in r.reasons do out := out ++ s!"      {x}\n"
  if r.verdict == "PASS" || r.verdict == "FAIL" then
    let severe := r.flags.filter (·.startsWith "severe: ")
    let axioms := r.flags.filter (·.startsWith "axiom ")
    let plain := r.flags.filter fun x => !(x.startsWith "severe: ") && !(x.startsWith "axiom ")
    -- counts by kind
    let isLib (x : String) := x.startsWith "content import" && (x.splitOn "feeding ante application").length > 1
    let isLoc (x : String) := (x.startsWith "bare-Prop local hypothesis" || x.startsWith "content-graded local fact")
                              && (x.splitOn "feeding ante application").length > 1
    let isRec (x : String) := (x.splitOn "inside a rewrite record").length > 1
    let isShape (x : String) := x.startsWith "goal-shaped local bridge"
    let isFactStep (x : String) := (x.splitOn "used as a step").length > 1
    let nLib := (plain.filter isLib).size
    let nLoc := (plain.filter isLoc).size
    let nRec := (plain.filter isRec).size
    let nShape := (plain.filter isShape).size
    let nFactStep := (plain.filter isFactStep).size
    let nOther := plain.size - nLib - nLoc - nRec - nShape - nFactStep
    if plain.isEmpty then out := out ++ "   warnings: none\n"
    else
      let mut parts : Array String := #[]
      if nLib > 0 then parts := parts.push s!"{nLib} library fact{if nLib == 1 then "" else "s"} meeting a hypothesis of the antecedent"
      if nLoc > 0 then parts := parts.push s!"{nLoc} local hypothes{if nLoc == 1 then "is" else "es"} meeting a hypothesis of the antecedent"
      if nRec > 0 then parts := parts.push s!"{nRec} library fact{if nRec == 1 then "" else "s"} inside a rewrite record or a local restatement's proof"
      if nShape > 0 then parts := parts.push s!"{nShape} goal-shaped local restatement{if nShape == 1 then "" else "s"}"
      if nFactStep > 0 then parts := parts.push s!"{nFactStep} library fact{if nFactStep == 1 then "" else "s"} with a ≠ or class conclusion used as a step"
      if nOther > 0 then parts := parts.push s!"{nOther} other"
      out := out ++ s!"   warnings: {plain.size} tolerated ({", ".intercalate parts.toList})\n"
    if severe.isEmpty then out := out ++ "   severe warnings: none\n"
    else
      out := out ++ s!"   severe warnings: {severe.size}\n"
      -- identical messages grouped, in first-occurrence order
      let mut seen : Array (String × Nat) := #[]
      for x in severe do
        let m := (x.drop 8).copy
        match seen.findIdx? (·.1 == m) with
        | some i => seen := seen.modify i fun (k, n) => (k, n + 1)
        | none => seen := seen.push (m, 1)
      for (m, n) in seen do
        out := out ++ s!"      {m}{if n > 1 then s!"   (×{n})" else ""}\n"
    if axioms.isEmpty then out := out ++ "   axioms beyond propext, Classical.choice, Quot.sound: none\n"
    else
      out := out ++ "   axioms beyond propext, Classical.choice, Quot.sound:\n"
      for x in axioms do
        let note := if (x.splitOn "native_decide").length > 1 then "   (native_decide)" else ""
        out := out ++ s!"      {x.drop 6}{note}\n"
  return out

/-- The file's own theorems in source order: every constant of the elaborated
file that a `theorem` or `lemma` command declared, whatever namespace,
attribute or visibility it carries, ordered by the position of its name. The
environment supplies the names and their positions; the source text is only
consulted for the keyword in front of each name and for the name itself, so
the auxiliary theorems Lean generates (equation lemmas, `injEq`,
`sizeOf_spec`) are never roles. -/
def declaredThms (env : Environment) (src : String) : Array Name := Id.run do
  let lines := (src.splitOn "\n").toArray
  let keywordBefore (line col : Nat) : Bool := Id.run do
    -- the text in front of the name on its own line, or, when the name opens
    -- a line, the end of the nearest non-blank line above it
    let mut l := line
    let mut pre := String.ofList ((lines[l - 1]?.getD "").toList.take col)
    while pre.trimAscii.isEmpty && l > 1 do
      l := l - 1
      pre := lines[l - 1]?.getD ""
    let t := pre.trimAsciiEnd.copy
    return t.endsWith "theorem" || t.endsWith "lemma"
  -- the identifier written at a position, and whether it is the name `n` as
  -- the file spells it (the last components of the full name)
  let spelledAt (line col endLine endCol : Nat) (n : Name) : Bool :=
    let rest := (lines[line - 1]?.getD "").toList.drop col
    let tok := String.ofList (if endLine == line then rest.take (endCol - col) else rest)
    let fits (full : String) : Bool := full == tok || full.endsWith ("." ++ tok)
    !tok.isEmpty && (fits (toString n) || fits (n.toString (escape := false)))
  let mut found : Array (Nat × Nat × Name) := #[]
  for (n, info) in env.constants.map₂.toList do
    unless info matches .thmInfo _ do continue
    let some r := declRangeExt.find? env n | continue
    let pos := r.selectionRange.pos
    let epos := r.selectionRange.endPos
    if keywordBefore pos.line pos.column
        && spelledAt pos.line pos.column epos.line epos.column n then
      found := found.push (pos.line, pos.column, n)
  let sorted := found.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  return sorted.map (·.2.2)

/-- Audit one fixture file. Fixture convention: the goal is the last theorem
with a real proof, the antecedent the last sorried theorem declared before
it, every other sorried theorem an assumed statement; the file needs at
least two theorems. The walk runs over the goal's proof term, then the axiom
accounting, then the reproof when no failure was recorded. -/
def auditFixture (path : String) (strict : Bool := false) : IO FixtureResult := do
  let src ← IO.FS.readFile path
  -- values of in-file theorems must be synchronously available for the term walk
  let compiled ← compileSide src path (opts := ({} : Options).setBool `Elab.async false)
  let some cmdState := compiled.cmdState?
    | return { file := path, verdict := "ERROR", reasons := compiled.report.errors }
  unless compiled.report.ok do
    return { file := path, verdict := "ERROR", reasons := compiled.report.errors }
  let env := cmdState.env
  let names := declaredThms env src
  if names.size < 2 then
    return { file := path, verdict := "ERROR",
             reasons := #[s!"expected ≥2 theorems, found {names.size}"] }
  let reachesSorryRaw (c : Name) : Bool :=
    match valueOf? env c (allowOpaque := true) with
    | some v => v.getUsedConstantsAsSet.contains ``sorryAx
    | none => true
  -- goal = the last non-sorried theorem; antecedent = the last sorried
  -- theorem declared before it; other sorried theorems = the assumed set
  let sorried := names.filter reachesSorryRaw
  let nonSorried := names.filter (fun n => !reachesSorryRaw n)
  let goal := nonSorried.back?.getD names.back!
  let goalIdx := (names.findIdx? (· == goal)).getD names.size
  let anteCands := sorried.filter fun n =>
    ((names.findIdx? (· == n)).getD names.size) < goalIdx
  let ante := anteCands.back?.getD (sorried.back?.getD names[0]!)
  let assumedArr := sorried.filter (· != ante)
  let assumed : NameSet := assumedArr.foldl (init := {}) (·.insert ·)
  let some goalVal := valueOf? env goal (allowOpaque := true)
    | return { file := path, verdict := "ERROR",
               reasons := #[s!"no value for goal theorem {goal}"], ante, goal }
  let goalType := ((env.find? goal).map (·.type)).getD (mkConst ``True)
  let goalConsts : NameSet :=
    goalType.getUsedConstantsAsSet.foldl (init := ({} : NameSet)) (·.insert ·)
  let goalPropCarrier :=
    (goalType.find? (fun e => e matches .sort .zero)).isSome
  let goalSortExists :=
    (goalType.find? (fun e =>
      e.isAppOfArity ``Exists 2 && (e.getArg! 0).isSort)).isSome
  let goalHasFin :=
    (goalType.find? (fun e => match e with
      | .forallE _ d _ _ => d.isAppOf `Finite || d.isAppOf `Fintype
      | _ => false)).isSome
  let ctx : Ctx := {
    env, ante, assumed, goalConsts, goalPropCarrier, goalSortExists, goalHasFin
    replayLocalFacts := !(← getConfig).noReplayLocalFacts
    witnessCheck := !(← getConfig).noWitnessCheck
    conjunctAblation := !(← getConfig).noConjunctAblation
    strictLocalProofs := strict || (← getConfig).strict
    conjunctSurface := !(← getConfig).noConjunctSurface
    goalStmt := goalType
    catMemo := ← IO.mkRef {}, reachMemo := ← IO.mkRef {}, sorryMemo := ← IO.mkRef {}
    localGrade := ← IO.mkRef {}, goalParts := ← IO.mkRef #[]
    occRoles := ← IO.mkRef {}, recordOccRoles := ← IO.mkRef {}, anteFVars := ← IO.mkRef {}, libraryFVars := ← IO.mkRef {}, recordHyps := ← IO.mkRef {}
    surfaceFVars := ← IO.mkRef {}, surfaceLeft := ← IO.mkRef 0
    anteSlotData := ← IO.mkRef #[], localValues := ← IO.mkRef {}
    propValues := ← IO.mkRef {}
    simpCache := ← IO.mkRef {}, whnfCache := ← IO.mkRef {}, involveMemo := ← IO.mkRef {}
    simpFuel := ← IO.mkRef 400000, simpExhausted := ← IO.mkRef false
    chainCtx := ← IO.mkRef 0, frozenCtx := ← IO.mkRef 0
    recordCtx := ← IO.mkRef 0, localProofCtx := ← IO.mkRef 0, localFactCtx := ← IO.mkRef 0, dirCtx := ← IO.mkRef 0, helperWalks := ← IO.mkRef {}
    goalOpenParts := ← IO.mkRef #[], goalTypeRem := ← IO.mkRef (mkConst ``True)
    fails := ← IO.mkRef #[], flags := ← IO.mkRef #[]
    sorryHit := ← IO.mkRef false, expanded := ← IO.mkRef {} }
  let opts : Options := (maxHeartbeats.set {} 4000000)
  try
    runMetaM env opts do
      ctx.goalParts.set (← computeGoalParts goalType)
      let anteType := ((env.find? ante).map (·.type)).getD (mkConst ``True)
      let anteData ← anteSlotKinds anteType
      ctx.anteSlotData.set anteData
      let dataTarget := anteData.foldl (fun n b => if b then n+1 else n) 0
      ctx.surfaceLeft.set (max (← extendedSurfaceDataArity goalType dataTarget) dataTarget)
      ctx.goalTypeRem.set goalType
      if ← reachesSorry ctx goalVal then
        ctx.sorryHit.set true    -- the goal proof itself is sorried
      else do
        if !(← anteInvolvedLB ctx goalVal) then
          ctx.fail "proof never touches the antecedent"
        walkLamSurface ctx .goal 0 goalVal
        -- axiom accounting: the three standard axioms and `sorryAx` (the
        -- assumed statements are sorried by protocol) are expected; a proof
        -- that depends on anything else (a local `axiom`, the compiler-trust
        -- axiom of `native_decide`) is not a valid proof for this audit: it
        -- is named and the proof fails
        for a in (← Lean.collectAxioms goal) do
          if a == ``propext || a == ``Classical.choice || a == ``Quot.sound || a == ``sorryAx then
            continue
          let here := if isLocalConst ctx.env a then " (declared in this file)" else ""
          ctx.flag s!"axiom {a} used by the proof{here}"
          ctx.fail s!"the proof depends on the axiom {a}{here}; only propext, Classical.choice and Quot.sound are accepted"
  catch e =>
    return { file := path, verdict := "ERROR",
             reasons := #[s!"audit crashed: {toString e}"], ante, goal,
             assumed := assumedArr }
  if ← ctx.sorryHit.get then
    return { file := path, verdict := "SKIP_SORRY", ante, goal, assumed := assumedArr }
  if ← ctx.simpExhausted.get then
    ctx.fails.modify (·.push "the proof is too large for the relevance check (simplification budget exhausted)")
  let mut fails ← ctx.fails.get
  let mut flags ← ctx.flags.get
  if fails.isEmpty then
    -- probe in the pristine import environment when possible: the fixture
    -- environment contains the proven goal and the sorried antecedent, which
    -- `exact?` would return as circular candidates; only possible when the
    -- goal's statement uses no fixture-local vocabulary
    let goalTypeClean := goalType.getUsedConstantsAsSet.toList.all
      fun c => !isLocalConst env c
    let reproofEnv ← do
      if goalTypeClean then
        try
          let inputCtx := Parser.mkInputContext src path
          let (header, _, _) ← Parser.parseHeader inputCtx
          let (cleanEnv, _) ← cachedImportModules (headerToImports header)
            (({} : Options).setBool `Elab.async false)
          pure cleanEnv
        catch _ => pure env
      else pure env
    let outcome ← try
        runTermElabM reproofEnv opts (confiscatedReproof ctx goal goalType goalVal)
      catch _ => pure ReproofOutcome.silent
    -- a bare-provable conclusion (the goal closes from the library alone) is
    -- a property of the pair, not of this proof: neither a conviction nor a
    -- report
    if outcome == .middleman then
      fails := fails.push
        "goal provable without the antecedent given the proof's own ante-free \
         local constructions (confiscated-instances reproof)"
  if fails.isEmpty then
    return { file := path, verdict := "PASS", flags, ante, goal, assumed := assumedArr }
  else
    return { file := path, verdict := "FAIL", flags, reasons := fails, ante, goal,
             assumed := assumedArr }

/-- Expand CLI paths: a directory contributes its immediate `*.lean` files except
`ref.lean`/`cand.lean`. -/
def expandPaths (paths : List String) : IO (Array String) := do
  let mut out := #[]
  for p in paths do
    if ← System.FilePath.isDir p then
      let entries ← System.FilePath.readDir p
      let files := entries.filterMap fun ent =>
        let n := ent.fileName
        if n.endsWith ".lean" && n != "ref.lean" && n != "cand.lean" then
          some ent.path.toString
        else none
      out := out ++ files.qsort (· < ·)
    else
      out := out.push p
  return out

/-- The `--proof` command: audit every fixture (a directory contributes its
`*.lean` files) and print each verdict, readable or as JSON with `--raw`. -/
def runProofCli (paths : List String) (raw : Bool := false) (strict : Bool := false) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: semanteq [--raw] --proof <fixture.lean|dir> [...]"
    return 1
  let files ← expandPaths paths
  for f in files do
    IO.eprintln s!"[proof-audit] {f}"
    let r ← auditFixture f (strict := strict)
    if raw then IO.println r.toJson.compress else IO.print r.render
    (← IO.getStdout).flush
  return 0
end ProofAudit
end SemantEq
