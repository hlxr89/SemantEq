import StaticEval.Driver

/-!
# BEq+ proof replay (`--replay`, 2026-08-21)

Measures toolchain drift by re-elaborating BEq+ v4.8's *accepting* proof
scripts on the current toolchain, inside this repo's own branched proving
environments. Input rows: `{id, dir ("r2c"|"c2r"), kind, script, reference,
candidate}` — `script` is the transcript's tactic text, which names the
antecedent `base_theorem` (BEq+'s adapter convention). The replay substitutes
the ante's fully-qualified name token-wise (preserving the original
implicit-argument structure — a `have`-alias would make every binder
explicit) and elaborates `by <script>` against the target statement type.

Outcomes per direction: `ok` (closes; drift-free), or `error` with the first
elaboration message (drift, classified downstream), or `pair-error` when the
pair itself does not reach a proving env (statement drift: uncompilable /
no-statement / merge failure).
-/

namespace StaticEval

open Lean Elab

/-- `tryScript` with the failure message kept (the replay's whole point is
WHY a v4.8 proof no longer elaborates). Multi-line scripts are laid out under
an indented `by` block (inline `by {script}` breaks the layout parser). -/
def tryScriptVerbose (goalType : Expr) (script : String)
    : Term.TermElabM (Except String Expr) := do
  let indented := String.intercalate "\n" ((script.splitOn "\n").map ("  " ++ ·))
  let src := s!"by\n{indented}"
  match Parser.runParserCategory (← getEnv) `term src with
  | .error e => return .error s!"PARSE: {e}"
  | .ok stx =>
    try
      -- fileMap aligned with the parsed string (ledger 29; see tryScript)
      withTheReader Core.Context (fun c => { c with fileMap := .ofString src }) do
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType stx goalType
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        if proof.hasSorry then return .error "ELAB: proof contains sorry"
        if proof.hasExprMVar then return .error "ELAB: unsolved metavariables"
        return .ok proof
    catch e =>
      return .error s!"ELAB: {← e.toMessageData.toString}"

/-- Whole-word `base_theorem` → fully-qualified ante name. -/
def substAnte (script : String) (ante : Name) : String := Id.run do
  let s := script
  let pat := "base_theorem"
  let mut out := ""
  let mut rest := s
  let isWord (c : Char) : Bool := c.isAlphanum || c == '_'
  while !rest.isEmpty do
    match rest.splitOn pat with
    | [] => break
    | [last] => out := out ++ last; rest := ""
    | first :: more =>
      let tail := String.intercalate pat more
      let prevOk := first.isEmpty || !(isWord (first.back))
      let nextOk := tail.isEmpty || !(isWord (tail.get 0))
      out := out ++ first ++ (if prevOk && nextOk then ante.toString else pat)
      rest := tail
  return out

/-- Number of PRE-COLON binder identifiers of the side's final `theorem`
declaration — the binders BEq+'s proof body had in scope. Counted
syntactically (the goal `Expr`'s forall telescope cannot distinguish
signature binders from arrow-form conclusion parts, which their scripts
`intro` themselves). -/
partial def preColonBinderCountImpl (env : Environment) (stmtText : String) : Nat := Id.run do
  match Parser.runParserCategory env `command stmtText with
  | .error _ => return 0
  | .ok stx =>
    -- find the declSig node, then count binder idents inside it
    let mut count := 0
    let sigKind := `Lean.Parser.Command.declSig
    let optSigKind := `Lean.Parser.Command.optDeclSig
    let binderKinds := [`Lean.Parser.Term.explicitBinder, `Lean.Parser.Term.implicitBinder,
                        `Lean.Parser.Term.strictImplicitBinder]
    let instKind := `Lean.Parser.Term.instBinder
    let rec countIn (x : Syntax) : Nat := Id.run do
      -- Syntax recursion: partial (no structural measure over getArgs)
      let mut n := 0
      if binderKinds.contains x.getKind then
        -- arg 1 is the ident group
        for c in x[1].getArgs do
          if c.isIdent || c.getKind == `Lean.Parser.Term.hole then n := n + 1
      else if x.getKind == instKind then
        n := n + 1
      else
        for c in x.getArgs do n := n + countIn c
      return n
    let rec findSig (x : Syntax) : Option Syntax :=
      if x.getKind == sigKind || x.getKind == optSigKind then some x
      else x.getArgs.findSome? findSig
    match findSig stx with
    | some sig => return countIn sig[0]  -- sig[0] = the binders, sig[1] = `: type`
    | none => return 0

/-- See `preColonBinderCountImpl`. -/
def preColonBinderCount (env : Environment) (stmtText : String) : Nat :=
  preColonBinderCountImpl env stmtText

/-- `intro` line for the goal's first `n` foralls, using each binder's recorded
user name where it is a valid plain identifier (their scripts reference these
names), fresh `_b<i>` otherwise (hygienic `inst✝`-style names are unwritable). -/
def introPrefix (goal : Expr) (n : Nat) : String := Id.run do
  if n == 0 then return ""
  let mut names : Array String := #[]
  let mut g := goal
  for i in [0:n] do
    match g with
    | .forallE nm _ body _ =>
      let s := nm.toString
      -- keep the user name unless it is hygienic/inaccessible; Lean identifiers
      -- are broad Unicode (φ, α, h₁), so no ASCII-only test (isAlpha is ASCII)
      let bad (c : Char) : Bool := c == '✝' || c == ' ' || c == '.' || c == '['
      let ok := !nm.hasMacroScopes && !s.isEmpty && !(s.get 0).isDigit &&
                !s.toList.any bad
      names := names.push (if ok then s else s!"_b{i}")
      g := body
    | _ => break
  if names.isEmpty then return ""
  return s!"intro {" ".intercalate names.toList}\n"

structure ReplayTask where
  id : String
  dir : String
  kind : String
  script : String
  reference : String
  candidate : String
  deriving Inhabited

def parseTask (j : Json) : Except String ReplayTask := do
  return { id := ← j.getObjValAs? String "id"
         , dir := ← j.getObjValAs? String "dir"
         , kind := ← j.getObjValAs? String "kind"
         , script := ← j.getObjValAs? String "script"
         , reference := ← j.getObjValAs? String "reference"
         , candidate := ← j.getObjValAs? String "candidate" }

/-- Replay every task of one pair. Mirrors `processPair`'s environment flow up
to `envA`/`envB`; no search, no audits — pure re-elaboration. -/
def replayPair (pid : String) (tasks : Array ReplayTask) : IO (Array Json) := do
  let mkErr (msg : String) : Array Json := tasks.map fun t =>
    Json.mkObj [("id", Json.str t.id), ("dir", Json.str t.dir),
                ("kind", Json.str t.kind), ("status", Json.str "pair-error"),
                ("error", Json.str msg)]
  let some t0 := tasks[0]? | return #[]
  let ref ← compileSide t0.reference s!"<{pid}.reference>"
  let cand ← compileSide t0.candidate s!"<{pid}.candidate>"
  match ref.cmdState?, cand.cmdState? with
  | some refSt, some candSt =>
    let refSrcE ← parseSide t0.reference s!"<{pid}.reference>"
    let candSrcE ← parseSide t0.candidate s!"<{pid}.candidate>"
    match refSrcE, candSrcE with
    | .ok refSrc, .ok candSrc =>
      let refIso? ← lastStatement? refSt.env
      let candIso? ← lastStatement? candSt.env
      match refIso?, candIso? with
      | some refIso, some candIso =>
        let ctx ← buildBranchedContext refSrc candSrc refIso.startPos candIso.startPos
          (candIsoName := candIso.fullName)
        match ctx.envA?, ctx.envB?, ctx.envFull? with
        | some envA, some envB, some env =>
          let refStmt? ← lastStatement? env (ns? := refNamespace)
          let candStmt? ← lastStatement? env (ns? := candNamespace)
          match refStmt?, candStmt? with
          | some refStmt, some candStmt =>
            let cmp ← compareStatements env refStmt.type candStmt.type
            let envA ← repairMissingAuxes env envA cmp.candExpr
            let envB ← repairMissingAuxes env envB cmp.refExpr
            -- the target side's statement TEXT (for the binder count): side input
            -- from the isolated compile's declaration start position
            let stmtTextOf (src : SideSource) (pos : Position) : String :=
              let fm := FileMap.ofString src.input
              (Substring.Raw.mk src.input (fm.ofPosition pos) src.input.rawEndPos).toString
            let refStmtText := stmtTextOf refSrc refIso.startPos
            let candStmtText := stmtTextOf candSrc candIso.startPos
            let candIntroN := preColonBinderCount env candStmtText
            let refIntroN := preColonBinderCount env refStmtText
            -- `open` commands from both preambles: BEq+'s shared-preamble file
            -- had them in scope; TermElabM has no command scopes, so re-apply
            -- them as openDecls (simple namespaces only — the PNV shape).
            let opensOf (src : String) : List Name :=
              (src.splitOn "\n").foldl (init := []) fun acc line =>
                let w := (line.splitOn " ").filter (!·.isEmpty)
                match w with
                | "open" :: rest =>
                  acc ++ (rest.takeWhile (· != "in")).map (·.toName)
                | _ => acc
            let opens := (opensOf refSrc.input ++ opensOf candSrc.input).eraseDups
            let openDecls := opens.map (OpenDecl.simple · [])
            let mut out : Array Json := #[]
            for t in tasks do
              let (penv, goal, ante, introN) :=
                if t.dir == "r2c" then (envA, cmp.candExpr, refStmt.fullName, candIntroN)
                else (envB, cmp.refExpr, candStmt.fullName, refIntroN)
              let script := introPrefix goal introN ++ substAnte t.script ante
              let res ← try
                  runTermElabM penv {} do
                    withTheReader Core.Context (fun c =>
                        { c with maxHeartbeats := 4000000 * 1000,
                                 openDecls := c.openDecls ++ openDecls }) do
                      tryScriptVerbose goal script
                catch e => pure (.error s!"DRIVER: {toString e}")
              out := out.push <| Json.mkObj
                [("id", Json.str t.id), ("dir", Json.str t.dir),
                 ("kind", Json.str t.kind),
                 ("status", Json.str (if res matches .ok _ then "ok" else "error")),
                 ("error", Json.str (match res with | .error m => (m.take 400).toString | _ => ""))]
            return out
          | _, _ => return mkErr "no-statement in merged env"
        | _, _, _ => return mkErr s!"ContextMergeError: {ctx.importErrors ++ ctx.refErrors ++ ctx.candErrors}"
      | _, _ => return mkErr "no-statement in isolated compile"
    | .error es, _ | _, .error es => return mkErr s!"parseSide: {es}"
  | _, _ =>
    return mkErr s!"side compile failed: ref={ref.report.errors} cand={cand.report.errors}"

def runReplay (inFile outFile : String) : IO UInt32 := do
  let lines := (← IO.FS.readFile inFile).splitOn "\n" |>.filter (!·.trim.isEmpty)
  let mut byPair : Array (String × Array ReplayTask) := #[]
  for l in lines do
    match Json.parse l >>= parseTask with
    | .error e => IO.eprintln s!"[replay] bad row skipped: {e}"
    | .ok t =>
      match byPair.findIdx? (·.1 == t.id) with
      | some i => byPair := byPair.modify i (fun (k, ts) => (k, ts.push t))
      | none => byPair := byPair.push (t.id, #[t])
  IO.eprintln s!"[replay] {lines.length} tasks over {byPair.size} pairs"
  let h ← IO.FS.Handle.mk outFile IO.FS.Mode.write
  let mut n := 0
  for (pid, ts) in byPair do
    n := n + 1
    IO.eprintln s!"[replay] ({n}/{byPair.size}) {pid}"
    let rows ← try replayPair pid ts
      catch e => pure <| ts.map fun t =>
        Json.mkObj [("id", Json.str t.id), ("dir", Json.str t.dir),
                    ("kind", Json.str t.kind), ("status", Json.str "pair-error"),
                    ("error", Json.str ((toString e |>.take 400).toString))]
    for r in rows do
      h.putStrLn r.compress
    h.flush
  return 0

end StaticEval
