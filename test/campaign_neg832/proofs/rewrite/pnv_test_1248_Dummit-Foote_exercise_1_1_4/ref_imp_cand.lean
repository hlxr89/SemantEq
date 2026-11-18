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
theorem dummy (n : ℕ) (a b c : ℕ) (ha : a ≠ 0) (h : a * b ≡ a * c [MOD n]) : b ≡ c [MOD n] := by
  -- not proved: the candidate statement is false; a nonzero factor need not be cancellable modulo n
  sorry
