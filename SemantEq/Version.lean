import Lean

/-!
# Program version stamp

`version` is the hand-maintained version tag — bump it whenever the search
behavior changes (new closer, guard, lemma-set change). Together with the git
commit captured at run time it stamps every out-file with a `_meta` first
record, so scored results stay attributable to the exact program that produced
them (`bench/HISTORY.jsonl` accumulates the scored history).
-/

namespace SemantEq

/-- Version tag of the search pipeline. Bump on any behaviour change: it stamps
every out-file's `_meta` record together with the git commit, so scored
results stay attributable to the program that produced them. -/
def version : String := "v1.3.0"

/-- Best-effort git identity of the working tree at run time: short commit hash
and whether the tree is dirty. `unknown` outside a git checkout. -/
def gitInfo : IO (String × Bool) := do
  try
    let head ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short", "HEAD"] }
    let dirty ← IO.Process.output { cmd := "git", args := #["status", "--porcelain"] }
    if head.exitCode != 0 then
      return ("unknown", false)
    return (head.stdout.trimAscii.copy, !dirty.stdout.trimAscii.copy.isEmpty)
  catch _ =>
    return ("unknown", false)

/-- The `_meta` record emitted as the first line of every run's output. -/
def metaRecord : IO Lean.Json := do
  let (git, dirty) ← gitInfo
  let date ← try
    let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
    pure out.stdout.trimAscii.copy
  catch _ => pure "unknown"
  return Lean.Json.mkObj
    [ ("_meta", Lean.Json.mkObj
        [ ("tool", "semanteq")
        , ("version", version)
        , ("git", git)
        , ("dirty", Lean.Json.bool dirty)
        , ("date", date) ]) ]

end SemantEq
