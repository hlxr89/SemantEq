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
  have hp_eq : p = 4 * (p / 4) + 1 := by
    have hdiv := Nat.mod_add_div p 4
    have hmod := hp1.out
    omega
  have htransport := exercise_4_4_assumed hp.out hp_eq (a : ZMod p)
  have hpgt : 2 < p := by
    have hmod := hp1.out
    have hp2 := hp.out.two_le
    omega
  constructor
  · intro h
    have hu : IsUnit (-a) := h.isUnit (by omega)
    rw [Int.isUnit_iff] at hu
    rcases hu with ha | ha
    · have haa : a = -1 := by omega
      subst a
      norm_num [IsPrimitiveRoot.iff_orderOf] at h
      omega
    · have haa : a = 1 := by omega
      subst a
      norm_num [IsPrimitiveRoot.iff_orderOf] at h
      omega
  · intro h
    have hu : IsUnit a := h.isUnit (by omega)
    rw [Int.isUnit_iff] at hu
    rcases hu with rfl | rfl <;> norm_num [IsPrimitiveRoot.iff_orderOf] at h <;> omega
