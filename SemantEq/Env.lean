namespace SemantEq

/-- Read a configuration variable. `SEMANTEQ_<name>` is the current spelling;
the pre-rename `STATIC_EVAL_<name>` is still honoured so existing scripts and
shells keep working. -/
def envVar (name : String) : IO (Option String) := do
  match ← IO.getEnv s!"SEMANTEQ_{name}" with
  | some v => return some v
  | none => IO.getEnv s!"STATIC_EVAL_{name}"

end SemantEq
