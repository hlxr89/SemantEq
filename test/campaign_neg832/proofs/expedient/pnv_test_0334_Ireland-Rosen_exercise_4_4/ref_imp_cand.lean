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
theorem dummy {p : ℕ} (hp : p.Prime) (h : ∃ t, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  obtain ⟨t, ht⟩ := h
  have impossible (x : ℤ) (hx : IsPrimitiveRoot x p) : False := by
    rcases (pow_eq_one_iff_of_ne_zero hp.ne_zero).mp hx.pow_eq_one with rfl | ⟨rfl, heven⟩
    · have hp_le : p ≤ 1 := Nat.le_of_dvd (by decide) (hx.dvd_of_pow_eq_one 1 (by simp))
      have := hp.two_le
      omega
    · obtain ⟨k, hk⟩ := heven
      omega
  constructor <;> intro ha
  · exact (impossible a ha).elim
  · exact (impossible (-a) ha).elim
