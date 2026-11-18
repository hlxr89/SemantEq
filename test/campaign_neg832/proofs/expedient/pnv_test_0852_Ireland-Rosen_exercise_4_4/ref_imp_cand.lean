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
theorem dummy {p : ℕ} [hp : Fact (Nat.Prime p)] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hpgt : 2 < p := by
    have := hp.out.two_le
    omega
  have no_root : ∀ z : ℤ, ¬ IsPrimitiveRoot z p := by
    intro z hz
    rcases Int.isUnit_iff.mp (hz.isUnit (by omega)) with rfl | rfl
    · exact (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
        (hz.dvd_of_pow_eq_one 1 (by simp))
    · exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hpgt)
        (hz.dvd_of_pow_eq_one 2 (by simp))
  exact ⟨fun h ↦ (no_root a h).elim, fun h ↦ (no_root (-a) h).elim⟩
