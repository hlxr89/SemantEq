import Mathlib

open scoped BigOperators

theorem dummy {x : ℝ} : x ≥ 1 → HasDerivAt (fun y => (y - 1)^2) 2 x := sorry
