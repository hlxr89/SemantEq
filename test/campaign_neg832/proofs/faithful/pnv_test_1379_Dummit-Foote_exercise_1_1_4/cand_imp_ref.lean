import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} : ∀ (a b c : ℤ), (a % n) * ((b % n) * (c % n)) = ((a % n) * (b % n)) % n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  -- not proved: direct transport is impossible; using the false antecedent via contradiction is forbidden by the proof-style rules
  sorry
