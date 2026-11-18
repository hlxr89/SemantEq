import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (h : Nat.Prime (2 ^ n + 1)) : IsPrimitiveRoot 3 (2 ^ n + 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  -- not proved: the assumption is about 3 in ℕ, while the goal is about 3 in ZMod p
  sorry
