import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_assumed {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p a : ℕ} (hp : p.Prime) (h : p = 4 * a + 1) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  constructor
  · intro ha
    have hua : IsUnit (-a : ℤ) := ha.isUnit hp.ne_zero
    rw [Int.isUnit_iff_abs_eq] at hua
    have ha1 : a = 1 := by simpa using hua
    subst a
    have := ha.pow_eq_one
    norm_num [h] at this
  · intro ha
    have ha1 : a = 1 := Nat.isUnit_iff.mp (ha.isUnit hp.ne_zero)
    subst a
    exfalso
    exact (ha.ne_one hp.one_lt) rfl
