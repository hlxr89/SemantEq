import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (m n k : ℕ) : (m * n) % k * k + m * n = m * (n * k) % k * k + m * (n % k * k + n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  -- not proved: a direct transport is impossible; the false antecedent can imply the goal only by forbidden explosion
  sorry
