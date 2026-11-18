import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble has local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (a b c : ℕ) (ha : a ≠ 0) (h : a * b ≡ a * c [MOD n]) : b ≡ c [MOD n] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  -- not proved: the statements are unrelated; using the false antecedent via contradiction would violate the required transport style
  sorry
