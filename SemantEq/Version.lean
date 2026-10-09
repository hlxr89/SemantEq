import Lean

/-!
# Program version stamp

`version` is bumped whenever the programs' behaviour changes (a new closer,
guard or lemma set). Together with the git commit captured at run time it
stamps every out-file with a `_meta` first record, so recorded results stay
attributable to the exact program that produced them.
-/

namespace SemantEq

/-- Version tag of the program; bump it on any behaviour change. -/
def version : String := "v1.4.0"

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
