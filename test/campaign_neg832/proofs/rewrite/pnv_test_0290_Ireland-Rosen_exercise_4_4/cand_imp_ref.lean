import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Fact (Prime p)) (hp1 : p % 4 = 1) (hp3 : p ≠ 3) (a : ℤ) (ha : a.gcd p = 1) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  -- not proved: the antecedent concerns ℤ, while the goal concerns ZMod p, and exact multiplicative order cannot be transported between these carrier types
  sorry
