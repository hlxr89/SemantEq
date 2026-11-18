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
theorem dummy {p : ℕ} (h : p.Prime) (hp : ∃ t : ℕ, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  obtain ⟨t, ht⟩ := hp
  have no_root (x : ℤ) : ¬ IsPrimitiveRoot x p := by
    intro hx
    rcases (pow_eq_one_iff_of_ne_zero h.ne_zero).mp hx.pow_eq_one with rfl | ⟨rfl, heven⟩
    · exact h.ne_one (Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by simp)))
    · apply (Nat.not_even_iff_odd.mpr ⟨2 * t, by omega⟩) heven
  exact iff_of_false (no_root a) (no_root (-a))
