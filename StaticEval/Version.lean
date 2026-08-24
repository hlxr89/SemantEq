import Lean

/-!
# Program version stamp

`version` is the hand-maintained milestone tag — bump it whenever the search
behavior changes (new closer, guard, lemma-set change). Together with the git
commit captured at run time it stamps every out-file with a `_meta` first
record, so scored results stay attributable to the exact program that produced
them (`bench/HISTORY.jsonl` accumulates the scored history).
-/

namespace StaticEval

/-- Milestone tag of the search pipeline. BUMP ON BEHAVIOR CHANGE.
v1.0.0 (2026-08-20): first ready-to-ship beta — closes the M4.x series
(P0 polarity, categorical audit grading, probe-0 rwStar staging, R1/R1(b)
instance packing, R6 transport discovery, R8' delayed-instance apply;
diagnostic tier retired — strict-only verdicts; search-strength env/CLI
knobs incl. the RD toggle). -/
def version : String := "v1.0.0"

/-- Best-effort git identity of the working tree at run time: short commit hash
and whether the tree is dirty. `unknown` outside a git checkout. -/
def gitInfo : IO (String × Bool) := do
  try
    let head ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short", "HEAD"] }
    let dirty ← IO.Process.output { cmd := "git", args := #["status", "--porcelain"] }
    if head.exitCode != 0 then
      return ("unknown", false)
    return (head.stdout.trim, !dirty.stdout.trim.isEmpty)
  catch _ =>
    return ("unknown", false)

/-- The `_meta` record emitted as the first line of every run's output. -/
def metaRecord : IO Lean.Json := do
  let (git, dirty) ← gitInfo
  let date ← try
    let out ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
    pure out.stdout.trim
  catch _ => pure "unknown"
  return Lean.Json.mkObj
    [ ("_meta", Lean.Json.mkObj
        [ ("tool", "static_eval")
        , ("version", version)
        , ("git", git)
        , ("dirty", Lean.Json.bool dirty)
        , ("date", date) ]) ]

end StaticEval
