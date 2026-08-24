import Lean
import StaticEval.Compile
import StaticEval.Statement

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

def buildBranchedContext (refSrc candSrc : SideSource)
    (refDeclStart candDeclStart : Position) (opts : Options := {})
    : IO BranchedContext := do
  match ← mkBaseEnv (unionImports refSrc.imports candSrc.imports) opts with
  | .error es => return { importErrors := es }
  | .ok base =>
  -- ref preamble: fresh state on base, wrapped in the ref namespace
  let sBase := Command.mkState base {} opts
  match ← elabResume sBase
      s!"namespace {refNamespace}
{refSrc.preambleBefore refDeclStart}"
      "<branch.ref.preamble>" with
  | .error es => return { refErrors := es }
  | .ok sRefPre =>
  -- cand preamble: fresh state (scopes must NOT leak across sides) on the grown env
  let sMid := Command.mkState sRefPre.env {} opts
  match ← elabResume sMid
      s!"namespace {candNamespace}
{candSrc.preambleBefore candDeclStart}"
      "<branch.cand.preamble>" with
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
