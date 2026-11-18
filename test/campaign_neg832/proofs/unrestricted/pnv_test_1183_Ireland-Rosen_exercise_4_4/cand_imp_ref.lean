import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : p = 4 * t + 1) (a : ℤ) (ha : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  constructor
  · intro ha
    have hlt := ZMod.orderOf_lt hp0.two_le a
    rw [← ha.eq_orderOf] at hlt
    omega
  · intro ha
    have hlt := ZMod.orderOf_lt hp0.two_le (-a)
    rw [← ha.eq_orderOf] at hlt
    omega
