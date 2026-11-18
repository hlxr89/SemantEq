import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℤ[X]) (hp1 : p.degree = 4) (hp2 : p.eval (-1) = 1) (hp3 : p.eval 1 = 1) : Irreducible p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  -- not proved: the reference polynomial has values 2 and 14 at -1 and 1, not 1 and 1
  sorry
