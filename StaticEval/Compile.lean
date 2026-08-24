import Lean

/-!
# Compiling one side of a pair (Milestone 1)

`compileSide` runs the full Lean frontend — header (imports) plus commands — on one raw
source string in a fresh, isolated environment, and reports whether it compiles. Error
messages are rendered into the report; user-level failures never throw.

The final `Command.State` is kept on the result so later milestones can extract the last
declared statement from the environment.
-/

namespace StaticEval

open Lean Elab

/-- Compile report for one side (reference or candidate) of a pair. -/
structure SideReport where
  ok     : Bool := false
  errors : Array String := #[]
  /-- The side was compiled inside a cached environment whose imports are a strict
  superset of the side's own header (see `cachedImportModules`): names beyond the
  declared imports were in scope. -/
  supersetEnv : Bool := false
deriving Inhabited

instance : ToJson SideReport where
  toJson r := Json.mkObj
    [ ("ok", Json.bool r.ok)
    , ("errors", Json.arr (r.errors.map Json.str))
    , ("supersetEnv", Json.bool r.supersetEnv) ]

/-- A compiled side: the report plus, when the frontend ran to completion, the final
command state (environment) for statement extraction in later milestones. -/
structure CompiledSide where
  report    : SideReport
  cmdState? : Option Command.State := none

private unsafe def enableInitializersExecutionUnsafe : IO Unit :=
  Lean.enableInitializersExecution

/-- `importModules (loadExts := true)` demands initializer execution to be enabled, and
`withImporting` resets the flag after every import — so it must be re-enabled before
*each* header import, not once at startup. Module initializers still run at most once
(`interpretedModInits` in `InitAttr.lean` caches them), so repeat imports are safe here
as long as processing stays single-threaded. -/
@[implemented_by enableInitializersExecutionUnsafe]
def enableInitializersExecution : IO Unit := pure ()

/-- Render the error-severity messages of a log. -/
def renderErrors (log : MessageLog) : BaseIO (Array String) := do
  let mut errs := #[]
  for msg in log.toArray do
    if msg.severity matches .error then
      errs := errs.push (← msg.toString)
  return errs

/-- Process-wide cache of imported base environments.

`importModules` on `import Mathlib` maps gigabytes of `.olean` regions and — because
`leakEnv := true` is required for initializer-execution safety — that memory is
never reclaimed. Without this cache every side compile and every shared context of
every pair paid (and leaked) a fresh full import: three per pair, unbounded across a
batch — enough to exhaust a 32 GB machine within a handful of `import Mathlib`
pairs.

Each entry stores the requested import set (the key), the environment's full
transitive module closure, and the environment. Lookup is **subset-collapsing**:
an exact key match is preferred, but otherwise ANY cached environment whose closure
covers the requested set is reused — `import Mathlib.Tactic` is served by the
`import Mathlib` environment rather than paying a second multi-gigabyte import.
A heterogeneous batch (e.g. gold statements with narrow imports vs candidates with
`import Mathlib`) then runs on one or two environments total instead of one per
distinct import set. The trade-off, chosen deliberately: a side compiled in a
superset environment has names in scope beyond its declared imports, so
import-sufficiency of the header is not checked (same behavior as BEq-style
evaluators, which run everything in one fat environment); such sides are flagged
`supersetEnv := true` in their report. The key ignores import flags
(`runtimeOnly` etc.) — the benchmark corpus only produces plain `import X`
headers. -/
initialize baseEnvCache : IO.Ref (Array (Array Name × NameSet × Environment)) ←
  IO.mkRef #[]

/-- Distinct base environments allowed per process (each costs gigabytes of leaked
memory). Overridable via `STATIC_EVAL_MAX_ENVS`; building one more past the cap
fails the requesting pair with a clear error instead of grinding the machine into
the OOM killer. -/
def maxBaseEnvs : IO Nat := do
  match (← IO.getEnv "STATIC_EVAL_MAX_ENVS").bind (·.toNat?) with
  | some n => return max n 1
  | none   => return 4

/-- Cached `importModules` with subset-collapsing lookup. Returns the environment
and whether it was a superset hit (imports beyond the requested set are in scope). -/
def cachedImportModules (imports : Array Import) (opts : Options)
    : IO (Environment × Bool) := do
  let key := (imports.map (·.module)).qsort (·.toString < ·.toString)
  let entries ← baseEnvCache.get
  for (k, _, env) in entries do
    if k == key then
      return (env, false)
  for (_, closure, env) in entries do
    if key.all closure.contains then
      return (env, true)
  if entries.size ≥ (← maxBaseEnvs) then
    throw <| IO.userError <|
      s!"refusing to build base environment #{entries.size + 1} for imports {key}: " ++
      "each distinct import set is a permanently-leaked multi-gigabyte importModules " ++
      "call. Raise STATIC_EVAL_MAX_ENVS or homogenize the batch's imports."
  IO.eprintln s!"[static_eval] importing (cache miss #{entries.size + 1}): {key}"
  -- leakEnv: cached initializer results may reference the compacted module regions,
  -- so they must never be freed once initializer execution is enabled.
  enableInitializersExecution
  let env ← importModules (leakEnv := true) (loadExts := true) (level := .private)
    imports opts (trustLevel := 1024)
  let closure : NameSet := env.allImportedModuleNames.foldl (·.insert ·) {}
  baseEnvCache.modify (·.push (key, closure, env))
  return (env, false)

/-- Run the full Lean frontend on `input` — a self-contained Lean source, imports
included — against the (cached) imported environment of its header. Imports are
resolved from the ambient `LEAN_PATH` (so run under `lake exe` / `lake env`). -/
def compileSide (input : String) (fileName : String := "<input>") (opts : Options := {})
    : IO CompiledSide := do
  let inputCtx := Parser.mkInputContext input fileName
  try
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    if messages.hasErrors then
      return { report := { ok := false, errors := ← renderErrors messages } }
    let (env, supersetEnv) ← cachedImportModules (headerToImports header) opts
    let cmdState := Command.mkState env messages opts
    let st ← IO.processCommands inputCtx parserState cmdState
    let errors ← renderErrors st.commandState.messages
    return { report := { ok := errors.isEmpty, errors, supersetEnv },
             cmdState? := some st.commandState }
  catch e =>
    return { report := { ok := false, errors := #[toString e] } }

end StaticEval
