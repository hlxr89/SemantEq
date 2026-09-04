import Lean
import StaticEval.Compile
import StaticEval.Statement
import StaticEval.PreambleMatch

/-!
# Per-pair contexts (Milestones 2.5 / 3.6)

The two sides of a pair are raw Lean files with their own imports and local
declarations. This module builds the environments the pipeline works in, all layered
over ONE base environment made from the **union of the two import sets**:

* the **comparison environment**: both sides' statements present, each side wrapped
  in its own namespace (`StaticEvalRef` / `StaticEvalCand`) so same-named local
  declarations don't clash. Used only to extract and compare the two statements.
* two **proving environments**, one per implication direction. Each contains the
  *antecedent* side in full — its statement is a genuine named theorem, usable via
  `apply`/`simp only [...]` — plus only the **preamble** of the target side (its local
  defs, so the goal is well-formed). The target statement itself is *absent*, so a
  proof can never refer to the very statement it is deriving: self-reference is
  structurally impossible rather than merely banned.

Since M4.9 all of these are BRANCHES of one stepwise build (`buildBranchedContext`,
diagrammed below at `BranchedContext`): the union imports and both preambles are
elaborated exactly ONCE into a shared base, and each statement is added by
resuming that side's preamble `Command.State` (`elabResume`) — no duplicate
elaboration of the local context.

When the two preambles are code-identical (comments/whitespace ignored) AND
declare constants (structures,
defs — the research-corpus shape), the preamble is elaborated once and BOTH
statements are phrased over the same copy (the shared-preamble path in
`buildBranchedContext`): two elaborations would mint two walled-off copies of
every local structure — distinct inductive types no proof can cross, failing
even the identity pair. Declaration-free preambles (`open`s/`variable`s only)
stay on the legacy two-namespace path.

The preamble/statement split uses the declaration range of the side's last statement
(found during the isolated Milestone-1 compile, so positions are in the original
file's coordinates). Anything after the final statement in a file is dropped from the
preamble.

Caveats, by design: the union env is more permissive than either side's own (an import
from one side could make a name ambiguous in the other — reported as
`ContextMergeError`, not silently absorbed); non-scoped notation declared by both
sides can clash; error positions in merged elaboration are offset by one line (the
`namespace` wrapper).
-/

namespace StaticEval

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

/-- The side's text from the end of the header up to (excluding) the declaration
starting at `declStart` — its local context, without its final statement. -/
def SideSource.preambleBefore (src : SideSource) (declStart : Position) : String :=
  let fileMap := (Parser.mkInputContext src.input "<pos>").fileMap
  let declPos := fileMap.ofPosition declStart
  (Substring.Raw.mk src.input src.headerEnd declPos).toString

/-- The side's text FROM the declaration starting at `declStart` to the end of the
file (trailing `end`s included) — the complement of `preambleBefore`. -/
def SideSource.statementFrom (src : SideSource) (declStart : Position) : String :=
  let fileMap := (Parser.mkInputContext src.input "<pos>").fileMap
  let declPos := fileMap.ofPosition declStart
  let text := (Substring.Raw.mk src.input declPos src.input.rawEndPos).toString
  -- M4.9: pad so the statement's declaration-range LINE exceeds every preamble
  -- declaration's — `lastStatement?` selects by source position, and a fragment
  -- elaborated from its own string would otherwise start at line 1 and lose to
  -- the preamble's defs (measured: NotAProposition on cw:01).
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

/-- Preamble equality is judged on CODE TOKENS: comments stripped, whitespace
runs collapsed. The research corpora's ref/cand preambles routinely differ in
prose (doc comments explaining each side's phrasing) while declaring identical
constants — byte comparison would silently miss every such pair (measured: all
6 mild candidates). A false EQUAL can only arise from the stripper mangling
code, and fails loudly downstream (the cand statement won't elaborate over the
ref preamble); a false DIFFERENT falls back to the legacy path. -/
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

/-- Does a preamble DECLARE anything (defs, structures, instances, lemmas)?
Opens/`variable`-only preambles mint no constants, so sharing them buys
nothing — such pairs stay on the legacy two-namespace path (keeps the entire
PNV-style corpus bit-compatible). Conservative line-prefix test; a false
negative merely falls back to the legacy path. -/
def declaringPreamble (pre : String) : Bool :=
  (pre.splitOn "\n").any fun l =>
    let l := l.trim
    [ "def ", "structure ", "inductive ", "class ", "abbrev ", "instance",
      "theorem ", "lemma ", "opaque ", "axiom ", "noncomputable ", "private ",
      "protected ", "@[", "mutual" ].any (·.isPrefixOf l)

/-- Shared-preamble path (post-v1.0.0 fix (a), research corpora): rewrite the
statement fragment's declaration head `theorem <name>`/`lemma <name>` to the
root-anchored `theorem _root_.StaticEvalCand.<iso-full-name>`, so the cand
statement can be elaborated while the REF preamble's scopes are open (sharing
its constants — one `IsBM`, not two walled-off copies) yet still land under
the cand namespace for extraction/self-absence. Rewrites the LAST occurrence
(doc comments precede the declaration) and checks the following char is not
an identifier char. `none` = head not found; caller falls back to the legacy
path. -/
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

/-- Drop trailing `end …` closer lines (and blanks) from a statement fragment.
Shared-preamble path only: both statements are elaborated from the PREAMBLE
state, and a fragment's trailing `end`s would pop the preamble's namespace
frame in the ENVIRONMENT's scoped-activation stack (per-branch scope lists are
copied, but activation is env-threaded) — killing scoped notation (`ℝ≥0`) for
every branch built over that env (measured: cwself:03 `<branch.full>`; the
legacy path survives only because its two preambles push duplicate frames).
Unclosed namespaces at fragment EOF are already the norm — the wrapper
namespace is never closed. -/
def stripTrailingEnds (fragment : String) : String :=
  let lines := (fragment.splitOn "\n").reverse
  let rec dropEnds : List String → List String
    | [] => []
    | l :: ls =>
      let t := l.trim
      if t.isEmpty || t == "end" || "end ".isPrefixOf t then dropEnds ls
      else l :: ls
  String.intercalate "\n" (dropEnds lines).reverse

/-- **M4.9-branch-env.** Elaborate `source` from an explicit `Command.State` —
scopes (open namespaces, `open`/`variable` declarations, sections) survive, so a
file can be elaborated in two stages: preamble first, statement later, WITHOUT
re-elaborating the preamble. Returns the final state for further resumption.
The message log is reset so errors are attributable to this stage. -/
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

/-- **M4.9-branch-env.** The branched environments of a pair. Everything grows from
ONE elaboration of each preamble:

```
env₀    = base ∪-imports + ref PREAMBLE + cand PREAMBLE     (statements absent)
envA    = env₀ + ref's statement    (proving env for ref → cand: ante present,
                                     target structurally ABSENT)
envB    = env₀ + cand's statement   (proving env for cand → ref)
envFull = envA + cand's statement   (comparison / extraction env)
```

Because environments are add-only and the branches EXTEND env₀, every preamble
constant — including every compiler-minted `_proof_N` auxiliary — exists under
the same name in every branch. The M4.8 Fix-0 mismatch class (preamble auxes
re-elaborated under different names in per-direction envs) is thereby impossible
rather than repaired; the transplant survives only for the rare residue of
auxiliaries minted by a STATEMENT's own type elaboration (those live only in
their branch, and the other direction's goal may reference them).

Statement elaboration RESUMES the side's preamble `Command.State` (with the env
swapped for the grown one), so open namespaces / `open` / `variable` scopes
carry across the split — the reason a naive two-pass split that re-elaborates
each fragment from scratch cannot work; see `elabResume`. -/
structure BranchedContext where
  envA?        : Option Environment := none
  envB?        : Option Environment := none
  envFull?     : Option Environment := none
  importErrors : Array String := #[]
  refErrors    : Array String := #[]
  candErrors   : Array String := #[]

/-- LEVEL 2 partial sharing (2026-08-25): elaborate the cand preamble
THROWAWAY beside the ref one, fixpoint-match declarations α-modulo-namespace
(`matchPreambles`), and build the remainder source (`candRemainder`) — the
cand preamble minus matched declarations, with `open` injections so shared
names resolve to the ref copies. `none` = don't share (no matches, nothing
deletable, or any failure) → the caller elaborates the full cand preamble
exactly as legacy. The throwaway environment is discarded; the real branch
chain never contains it. -/
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
    if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
      IO.eprintln s!"[context] level-2 partial share: {matched.toList.length} decls matched, {deletable.size} chunks shared, remainder {rem.length}B"
    return some rem
  catch _ => return none

def buildBranchedContext (refSrc candSrc : SideSource)
    (refDeclStart candDeclStart : Position) (opts : Options := {})
    (candIsoName : Name := .anonymous)
    : IO BranchedContext := do
  match ← mkBaseEnv (unionImports refSrc.imports candSrc.imports) opts with
  | .error es => return { importErrors := es }
  | .ok base =>
  let refPre := refSrc.preambleBefore refDeclStart
  -- Shared-preamble path (fix (a)): when both preambles are code-identical AND
  -- actually declare constants, elaborating them twice would mint two
  -- walled-off copies of every local structure (distinct inductive types — no
  -- proof can cross; even the identity pair fails). Instead the preamble is
  -- elaborated ONCE (ref namespace) and the cand statement is elaborated in
  -- the ref preamble's scopes with its declaration root-anchored under the
  -- cand namespace (`rootAnchorDecl`), so both statements are phrased over
  -- the SAME preamble constants while extraction and self-absence keep their
  -- per-side namespaces. Declaration-free preambles stay on the legacy path.
  let candPre := candSrc.preambleBefore candDeclStart
  let gNorm := normalizeCode refPre == normalizeCode candPre
  let gDecl := declaringPreamble refPre
  let sharedCandStmt? : Option String :=
    if candIsoName != .anonymous && gNorm && gDecl then
      rootAnchorDecl (candSrc.statementFrom candDeclStart) candIsoName
    else none
  if gDecl then  -- diagnostic: only declaring preambles are sharing candidates
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
    -- SHARED: env₀ = base + one preamble; both branches extend it directly.
    -- Trailing `end`s are stripped from BOTH fragments — see `stripTrailingEnds`.
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
  -- cand preamble: fresh state (scopes must NOT leak across sides) on the grown
  -- env. LEVEL 2 first: on a partial α-modulo-namespace match the source is
  -- the REMAINDER (matched declarations shared from the ref copy); any
  -- level-2 failure — including the remainder failing to elaborate — falls
  -- back to the full legacy text.
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
        if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
          IO.eprintln s!"[context] level-2 remainder failed to elaborate — legacy fallback ({es.size} errors)"
        elabResume sMid s!"namespace {candNamespace}
{candPreFull}" "<branch.cand.preamble>"
    | none =>
      elabResume sMid s!"namespace {candNamespace}
{candPreFull}" "<branch.cand.preamble>"
  match sCandPreE with
  | .error es => return { candErrors := es }
  | .ok sCandPre =>
  -- envB: cand's statement, RESUMING cand's preamble scopes (env already = env₀)
  match ← elabResume sCandPre (candSrc.statementFrom candDeclStart)
      "<branch.cand.stmt>" with
  | .error es => return { candErrors := es }
  | .ok sB =>
  -- envA: ref's statement, resuming REF's preamble scopes over env₀
  match ← elabResume { sRefPre with env := sCandPre.env }
      (refSrc.statementFrom refDeclStart) "<branch.ref.stmt>" with
  | .error es => return { refErrors := es }
  | .ok sA =>
  -- envFull: cand's statement over envA (comparison env; second elaboration of
  -- ONE single theorem — the accepted residual, covered by the Fix-0 transplant)
  match ← elabResume { sCandPre with env := sA.env }
      (candSrc.statementFrom candDeclStart) "<branch.full>" with
  | .error es => return { candErrors := es }
  | .ok sFull =>
  return { envA? := some sA.env, envB? := some sB.env,
           envFull? := some sFull.env }

end StaticEval
