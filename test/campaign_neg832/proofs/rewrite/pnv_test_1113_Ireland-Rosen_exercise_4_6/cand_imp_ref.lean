import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (h : Nat.Prime p ∧ ∃ (n : ℕ), p = 2^n + 1) : IsPrimitiveRoot 3 p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  -- not proved: the assumption is about (3 : ℕ), while the goal is about (3 : ZMod p)
  sorry
