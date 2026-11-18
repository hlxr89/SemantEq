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
theorem dummy {p : ℕ} [hp : Fact p.Prime] [hp1 : Fact (p % 4 = 1)] (a : ℤ) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  have hp_ge2 : 2 ≤ p := hp.out.two_le
  have hmod : p % 4 = 1 := hp1.out
  have hp2 : 2 < p := by omega
  have no_root (x : ℤ) : ¬ IsPrimitiveRoot x p := by
    intro h
    have hx : IsUnit x := h.isUnit (by omega)
    exact Nat.not_dvd_of_pos_of_lt (by omega) hp2 (h.dvd_of_pow_eq_one 2 (Int.isUnit_sq hx))
  exact iff_of_false (no_root (-a)) (no_root a)
