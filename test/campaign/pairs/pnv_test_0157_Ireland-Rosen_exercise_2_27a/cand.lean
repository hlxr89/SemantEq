import Mathlib

open Real
open scoped BigOperators

theorem dummy : ¬ Summable (fun n => if H : Squarefree n then 1 / n else 0) := sorry
