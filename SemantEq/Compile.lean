import Lean
import SemantEq.Config

/-!
# Compiling one side of a pair

`compileSide` runs the Lean frontend, header and commands, on one raw source
string in a fresh environment and reports whether it compiles. Error messages
are rendered into the report; user-level failures never throw. The final
command state is kept on the result so later stages can extract the last
declared statement from it.
-/

namespace SemantEq
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

/-- A compiled side: the report plus, when the frontend ran to completion, the final
command state (environment) for statement extraction in the later stages. -/
structure CompiledSide where
  report    : SideReport
  cmdState? : Option Command.State := none
private unsafe def enableInitializersExecutionUnsafe : IO Unit :=
  Lean.enableInitializersExecution

/-- `importModules (loadExts := true)` requires initializer execution to be
enabled, and `withImporting` resets the flag after every import, so it must be
re-enabled before each header import, not once at start-up. Module
initializers still run at most once (`interpretedModInits` caches them), so
repeated imports are safe while processing stays single-threaded. -/
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

`importModules` on `import Mathlib` maps gigabytes of `.olean` regions that
are never reclaimed (`leakEnv := true` is required for initializer safety), so
every distinct import set is built at most once per process. Each entry holds
the requested import set (the key), the environment's transitive module
closure and the environment. Lookup collapses subsets: an exact match is
preferred, otherwise any cached environment whose closure covers the request
is reused, so `import Mathlib.Tactic` is served by the `import Mathlib`
environment. A side compiled in such a superset environment has names in
scope beyond its declared imports, so import sufficiency of its header is not
checked; its report says `supersetEnv := true`. The key ignores import flags
such as `runtimeOnly`. -/
initialize baseEnvCache : IO.Ref (Array (Array Name × NameSet × Environment)) ←
  IO.mkRef #[]

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
  if entries.size ≥ (← getConfig).maxEnvs then
    throw <| IO.userError <|
      s!"refusing to build base environment #{entries.size + 1} for imports {key}: " ++
      "each distinct import set is a permanently-leaked multi-gigabyte importModules " ++
      "call. Raise SEMANTEQ_MAX_ENVS or homogenize the batch's imports."
  IO.eprintln s!"[semanteq] importing (cache miss #{entries.size + 1}): {key}"
  -- leakEnv: cached initializer results may reference the compacted module regions,
  -- so they must never be freed once initializer execution is enabled.
  enableInitializersExecution
  let env ← importModules (leakEnv := true) (loadExts := true) (level := .private)
    imports opts (trustLevel := 1024)
  let closure : NameSet := env.allImportedModuleNames.foldl (·.insert ·) {}
  baseEnvCache.modify (·.push (key, closure, env))
  return (env, false)

/-- Run the full Lean frontend on `input`, a self-contained Lean source with
its imports, against the cached environment of its header. Imports are
resolved from the ambient `LEAN_PATH`, so run under `lake exe` or `lake env`. -/
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
end SemantEq
