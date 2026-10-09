import Lean
import SemantEq.Compile
import SemantEq.Statement
import SemantEq.PreambleMatch
import SemantEq.Config

/-!
# Per-pair environments

A pair arrives as two raw Lean files with their own imports and local
declarations. This module builds the environments the pipeline works in, all
layered over one base environment made from the union of the two import sets:

* the comparison environment holds both statements, each side under its own
  namespace (`SemantEqRef`, `SemantEqCand`) so same-named local declarations
  do not clash; it is used only to extract and compare the two statements;
* one proving environment per implication direction holds the antecedent
  side in full (its statement is a named theorem, usable by `apply` and
  `simp only`) and only the preamble of the target side, so the goal is well
  formed while the target statement itself is absent: a proof cannot refer to
  the statement it derives.

`buildBranchedContext` elaborates the union imports and both preambles once
into a shared base and adds each statement by resuming that side's command
state. Preambles that are code-identical and declare constants are elaborated
once and shared by both sides (`PreambleMatch` covers the partially identical
case), because two elaborations would produce two distinct copies of every
local structure that no proof could relate. Otherwise each side keeps its own
namespace.

A side's preamble ends at the declaration range of its final statement, found
during the isolated compile; anything after that statement is dropped. Known
limits: the union environment is more permissive than either side's own (an
import from one side can make a name ambiguous in the other, reported as
`ContextMergeError`); non-scoped notation declared by both sides can clash;
error positions in merged elaboration are offset by the `namespace` line.
-/

namespace SemantEq
open Lean Elab

/-- One side split into its import header and the source text after it. -/
structure SideSource where
  imports   : Array Import
  body      : String
  /-- The full original text (positions from the isolated compile refer to this). -/
  input     : String
  /-- Where the header ends in `input`. -/
  headerEnd : String.Pos.Raw

/-- Parse a side's header without building an environment. -/
def parseSide (input : String) (fileName : String) : IO (Except (Array String) SideSource) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    return .error (← renderErrors messages)
  let headerEnd := parserState.pos
  let body := (Substring.Raw.mk input headerEnd input.rawEndPos).toString
  return .ok { imports := headerToImports header, body, input, headerEnd }

/-- The side's text from the end of the header up to (excluding) the
declaration starting at `declStart`: its local context without its final
statement. -/
def SideSource.preambleBefore (src : SideSource) (declStart : Position) : String :=
  let fileMap := (Parser.mkInputContext src.input "<pos>").fileMap
  let declPos := fileMap.ofPosition declStart
  (Substring.Raw.mk src.input src.headerEnd declPos).toString

/-- The side's text from the declaration starting at `declStart` to the end of
the file, trailing `end`s included: the complement of `preambleBefore`. -/
def SideSource.statementFrom (src : SideSource) (declStart : Position) : String :=
  let fileMap := (Parser.mkInputContext src.input "<pos>").fileMap
  let declPos := fileMap.ofPosition declStart
  let text := (Substring.Raw.mk src.input declPos src.input.rawEndPos).toString
  -- blank lines keep the statement at its original line number: `lastStatement?`
  -- selects by source position, and a fragment elaborated from its own string
  -- would otherwise start at line 1 and lose to the preamble's declarations
  String.join (List.replicate (declStart.line + 1) "
") ++ text

/-- Union of both sides' imports, deduplicated by module name. -/
def unionImports (a b : Array Import) : Array Import := Id.run do
  let mut seen : NameSet := {}
  let mut imports : Array Import := #[]
  for i in a ++ b do
    unless seen.contains i.module do
      seen := seen.insert i.module
      imports := imports.push i
  return imports

/-- Build the base environment for a pair from the union import set. -/
def mkBaseEnv (imports : Array Import) (opts : Options := {})
    : IO (Except (Array String) Environment) := do
  try
    return .ok (← cachedImportModules imports opts).1
  catch e =>
    return .error #[toString e]


/-- Error payload of a failed `buildBranchedContext`, reported to the driver's
JSON under `"context"` as a `ContextMergeError`; the populated field identifies
the stage that failed. -/
structure SharedContext where
  importErrors : Array String := #[]
  refErrors    : Array String := #[]
  candErrors   : Array String := #[]



/-- Comment stripper for `normalizeCode`: drops nested `/- … -/` blocks (doc
comments included) and `--` line comments; string literals are copied verbatim
(a `--` inside one is not a comment). `depth` = block-comment nesting,
`inStr` = inside a string literal. -/
private partial def stripCommentsAux : List Char → Nat → Bool → List Char
  | [], _, _ => []
  | '\\' :: d :: tl, 0, true => '\\' :: d :: stripCommentsAux tl 0 true
  | '"' :: tl, 0, true => '"' :: stripCommentsAux tl 0 false
  | c :: tl, 0, true => c :: stripCommentsAux tl 0 true
  | '/' :: '-' :: tl, d, false => stripCommentsAux tl (d+1) false
  | '-' :: '/' :: tl, d+1, false => stripCommentsAux tl d false
  | _ :: tl, d+1, false => stripCommentsAux tl (d+1) false
  | '-' :: '-' :: tl, 0, false => stripCommentsAux (tl.dropWhile (· != '\n')) 0 false
  | '"' :: tl, 0, false => '"' :: stripCommentsAux tl 0 true
  | c :: tl, 0, false => c :: stripCommentsAux tl 0 false
  | c :: tl, d+1, true => c :: stripCommentsAux tl (d+1) true -- unreachable: strings never open inside comments

/-- Preamble equality is judged on code tokens: comments stripped, whitespace
runs collapsed, so two preambles that differ only in prose compare equal. A
false "equal" could only come from the stripper mangling code and fails
loudly downstream (the candidate statement would not elaborate over the
reference preamble); a false "different" only forgoes the sharing. -/
def normalizeCode (s : String) : String := Id.run do
  let stripped := stripCommentsAux s.toList 0 false
  let mut out := ""
  let mut pendingWs := false
  for c in stripped do
    if c.isWhitespace then
      pendingWs := true
    else
      if pendingWs && !out.isEmpty then out := out.push ' '
      pendingWs := false
      out := out.push c
  return out

/-- Does a preamble declare anything (defs, structures, instances, lemmas)? A
preamble of `open` and `variable` lines mints no constants, so sharing it buys
nothing and such pairs keep one namespace per side. A conservative line-prefix
test; a false negative only forgoes the sharing. -/
def declaringPreamble (pre : String) : Bool :=
  (pre.splitOn "\n").any fun l =>
    let l := l.trimAscii.copy
    [ "def ", "structure ", "inductive ", "class ", "abbrev ", "instance",
      "theorem ", "lemma ", "opaque ", "axiom ", "noncomputable ", "private ",
      "protected ", "@[", "mutual" ].any (·.isPrefixOf l)

/-- Shared-preamble path: rewrite the statement fragment's declaration head
`theorem <name>` or `lemma <name>` to the root-anchored
`theorem _root_.SemantEqCand.<full name>`, so the candidate statement
elaborates while the reference preamble's scopes are open (sharing its
constants) and still lands under the candidate namespace for extraction and
self-absence. The last occurrence is rewritten (doc comments precede the
declaration) and the following character must not continue an identifier.
`none` when the head is not found; the caller then keeps one namespace per
side. -/
def rootAnchorDecl (fragment : String) (isoFullName : Name) : Option String := Id.run do
  let lastComp := match isoFullName with
    | .str _ s => s
    | _ => ""
  if lastComp.isEmpty then return none
  for kw in ["theorem ", "lemma "] do
    let pat := kw ++ lastComp
    let parts := fragment.splitOn pat
    if parts.length ≥ 2 then
      let tail := parts.getLast!
      let boundaryOk := tail.isEmpty ||
        (let c := tail.front
         !(c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'))
      if boundaryOk then
        let newHead := kw ++ "_root_." ++ (candNamespace ++ isoFullName).toString
        return some (String.intercalate pat parts.dropLast ++ newHead ++ tail)
  return none

/-- Drop trailing `end` lines (and blanks) from a statement fragment. On the
shared-preamble path both statements are elaborated from the preamble's
state, and a fragment's trailing `end`s would pop the preamble's namespace
frame from the environment's activation stack, which disables scoped notation
such as `ℝ≥0` for every branch built over that environment. Leaving
namespaces open at the end of a fragment is harmless; the wrapper namespace
is never closed either. -/
def stripTrailingEnds (fragment : String) : String :=
  let lines := (fragment.splitOn "\n").reverse
  let rec dropEnds : List String → List String
    | [] => []
    | l :: ls =>
      let t := l.trimAscii.copy
      if t.isEmpty || t == "end" || "end ".isPrefixOf t then dropEnds ls
      else l :: ls
  String.intercalate "\n" (dropEnds lines).reverse

/-- Elaborate `source` from an explicit command state, so scopes (open
namespaces, `open` and `variable` declarations, sections) survive and a file
can be elaborated in two stages, preamble first and statement later, without
re-elaborating the preamble. Returns the final state for further resumption;
the message log is reset so errors are attributable to this stage. -/
def elabResume (state : Command.State) (source : String) (fileName : String)
    : IO (Except (Array String) Command.State) := do
  let inputCtx := Parser.mkInputContext source fileName
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    return .error (← renderErrors messages)
  let st ← IO.processCommands inputCtx parserState { state with messages := messages }
  let errors ← renderErrors st.commandState.messages
  if errors.isEmpty then
    return .ok st.commandState
  return .error errors

/-- The branched environments of a pair. Everything grows from one
elaboration of each preamble:

```
env₀    = base (union imports) + reference preamble + candidate preamble
envA    = env₀ + reference statement   (proving environment for ref → cand)
envB    = env₀ + candidate statement   (proving environment for cand → ref)
envFull = envA + candidate statement   (comparison and extraction environment)
```

Environments are add-only and every branch extends env₀, so every preamble
constant, including every compiler-generated `_proof_N` auxiliary, exists
under the same name in every branch. Only auxiliaries minted by a statement's
own elaboration live in one branch alone (`repairMissingAuxes` covers those).
Statement elaboration resumes the side's preamble command state with the
grown environment, so the preamble's scopes carry across the split
(`elabResume`). -/
structure BranchedContext where
  envA?        : Option Environment := none
  envB?        : Option Environment := none
  envFull?     : Option Environment := none
  importErrors : Array String := #[]
  refErrors    : Array String := #[]
  candErrors   : Array String := #[]

/-- Partial sharing: elaborate the candidate preamble in a throwaway state
beside the reference one, match declarations modulo the namespace to a
fixpoint (`matchPreambles`), and build the remainder source
(`candRemainder`): the candidate preamble without the matched declarations,
with `open` lines so shared names resolve to the reference copies. `none`
when nothing matches, nothing is deletable or anything fails; the caller then
elaborates the full candidate preamble. The throwaway environment never enters
the branch chain. -/
def tryPartialShare (base : Environment) (sRefPre : Command.State)
    (candPre : String) (opts : Options) : IO (Option String) := do
  try
    let sMidT := Command.mkState sRefPre.env {} opts
    match ← elabResume sMidT s!"namespace {candNamespace}
{candPre}" "<level2.throwaway>" with
    | .error _ => return none
    | .ok sT =>
    let matched ← runMetaM sT.env opts (matchPreambles sT.env candNamespace refNamespace)
    if matched.isEmpty then return none
    let some chunks ← chunkPreamble base opts candPre | return none
    let deletable := chunks.filter (fun c => c.name?.any matched.contains)
    if deletable.isEmpty then return none
    let rem := candRemainder refNamespace chunks matched
    if (← getConfig).trace then
      IO.eprintln s!"[context] level-2 partial share: {matched.toList.length} decls matched, {deletable.size} chunks shared, remainder {rem.length}B"
    return some rem
  catch _ => return none

/-- Build the branched environments of a pair from the two sides' sources and
the start positions of their final statements. When both preambles are
code-identical and declare constants, the preamble is elaborated once under
the reference namespace and the candidate statement is elaborated in its
scopes with the declaration root-anchored under the candidate namespace
(`rootAnchorDecl`), so both statements are phrased over the same local
constants. When the preambles declare constants but differ, the matching
declarations are shared (`tryPartialShare`) and the candidate's remainder is
elaborated in its own namespace. Otherwise each side keeps its own namespace.
`candIsoName` is the candidate statement's full name from its isolated
compile; when it is anonymous, neither sharing path runs. -/
def buildBranchedContext (refSrc candSrc : SideSource)
    (refDeclStart candDeclStart : Position) (opts : Options := {})
    (candIsoName : Name := .anonymous)
    : IO BranchedContext := do
  match ← mkBaseEnv (unionImports refSrc.imports candSrc.imports) opts with
  | .error es => return { importErrors := es }
  | .ok base =>
  let refPre := refSrc.preambleBefore refDeclStart
  -- the shared-preamble path (see the doc comment above)
  let candPre := candSrc.preambleBefore candDeclStart
  let gNorm := normalizeCode refPre == normalizeCode candPre
  let gDecl := declaringPreamble refPre
  let sharedCandStmt? : Option String :=
    if candIsoName != .anonymous && gNorm && gDecl then
      rootAnchorDecl (candSrc.statementFrom candDeclStart) candIsoName
    else none
  if gDecl && (← getConfig).trace then  -- only declaring preambles are sharing candidates
    IO.eprintln s!"[context] shared-preamble gate: norm-eq={gNorm} anchored={sharedCandStmt?.isSome}"
  -- ref preamble: fresh state on base, wrapped in the ref namespace
  let sBase := Command.mkState base {} opts
  match ← elabResume sBase
      s!"namespace {refNamespace}
{refPre}"
      "<branch.ref.preamble>" with
  | .error es => return { refErrors := es }
  | .ok sRefPre =>
  match sharedCandStmt? with
  | some candStmtSrc =>
    -- shared: env₀ = base + one preamble; both branches extend it directly.
    -- Trailing `end`s are stripped from both fragments (`stripTrailingEnds`).
    let candStmtSrc := stripTrailingEnds candStmtSrc
    match ← elabResume sRefPre candStmtSrc "<branch.cand.stmt>" with
    | .error es => return { candErrors := es }
    | .ok sB =>
    match ← elabResume sRefPre (stripTrailingEnds (refSrc.statementFrom refDeclStart))
        "<branch.ref.stmt>" with
    | .error es => return { refErrors := es }
    | .ok sA =>
    match ← elabResume { sRefPre with env := sA.env } candStmtSrc
        "<branch.full>" with
    | .error es => return { candErrors := es }
    | .ok sFull =>
    return { envA? := some sA.env, envB? := some sB.env,
             envFull? := some sFull.env }
  | none =>
  -- candidate preamble: a fresh state (scopes must not leak across sides) on
  -- the grown environment; partial sharing first, the full text as fallback
  let candPreFull := candSrc.preambleBefore candDeclStart
  let level2? ←
    if candIsoName != .anonymous && declaringPreamble refPre
        && declaringPreamble candPreFull then
      tryPartialShare base sRefPre candPreFull opts
    else pure none
  let sMid := Command.mkState sRefPre.env {} opts
  let sCandPreE ← do
    match level2? with
    | some rem =>
      match ← elabResume sMid s!"namespace {candNamespace}
{rem}" "<branch.cand.preamble>" with
      | .ok st => pure (Except.ok st)
      | .error es =>
        if (← getConfig).trace then
          IO.eprintln s!"[context] level-2 remainder failed to elaborate — legacy fallback ({es.size} errors)"
        elabResume sMid s!"namespace {candNamespace}
{candPreFull}" "<branch.cand.preamble>"
    | none =>
      elabResume sMid s!"namespace {candNamespace}
{candPreFull}" "<branch.cand.preamble>"
  match sCandPreE with
  | .error es => return { candErrors := es }
  | .ok sCandPre =>
  -- envB: the candidate statement, resuming the candidate preamble's scopes
  match ← elabResume sCandPre (candSrc.statementFrom candDeclStart)
      "<branch.cand.stmt>" with
  | .error es => return { candErrors := es }
  | .ok sB =>
  -- envA: the reference statement, resuming the reference preamble's scopes
  match ← elabResume { sRefPre with env := sCandPre.env }
      (refSrc.statementFrom refDeclStart) "<branch.ref.stmt>" with
  | .error es => return { refErrors := es }
  | .ok sA =>
  -- envFull: the candidate statement over envA (the comparison environment)
  match ← elabResume { sCandPre with env := sA.env }
      (candSrc.statementFrom candDeclStart) "<branch.full>" with
  | .error es => return { candErrors := es }
  | .ok sFull =>
  return { envA? := some sA.env, envB? := some sB.env,
           envFull? := some sFull.env }
end SemantEq
