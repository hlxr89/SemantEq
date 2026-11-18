import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_4_assumed (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {n : ℕ} : ∀ (a b c : ℤ), (a % n) * (b % n) = (a * b) % n := by
  -- not proved: the statement is false, for example when n = 5 and a = b = 3
  sorry
