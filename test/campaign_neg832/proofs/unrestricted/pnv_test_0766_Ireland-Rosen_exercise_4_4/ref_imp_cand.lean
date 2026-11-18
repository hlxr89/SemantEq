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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have no_root : ∀ b : ℤ, ¬ IsPrimitiveRoot b p := by
    intro b hb
    rcases (pow_eq_one_iff_of_ne_zero hp.out.ne_zero).mp hb.pow_eq_one with hbone | ⟨hbneg, heven⟩
    · subst b
      exact hp.out.not_dvd_one (hb.dvd_of_pow_eq_one 1 (by simp))
    · obtain ⟨k, hk⟩ := heven
      omega
  exact ⟨fun h ↦ (no_root a h).elim, fun h ↦ (no_root (-a) h).elim⟩
