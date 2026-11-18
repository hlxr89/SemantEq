import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Ring R] [IsDomain R] (f : R[X]) (h : f = X ^ 4 - 4 * X ^ 3 + 6) : ¬ ∃ (p q : R[X]), p * q = f ∧ 0 < degree p ∧ 0 < degree q := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  let fQ : ℚ[X] := X ^ 4 - 4 * X ^ 3 + 6
  have h_no_factor : ¬ ∃ (p q : ℚ[X]), p * q = fQ ∧ 0 < degree p ∧ 0 < degree q :=
    dummy_assumed fQ rfl
  have hfQ_ne : fQ ≠ 0 := by
    intro hzero
    have := congrArg (fun p : ℚ[X] => p.coeff 0) hzero
    norm_num [fQ] at this
  have hfQ_irred : Irreducible fQ := by
    rw [irreducible_iff]
    constructor
    · intro hu
      have hdeg : degree fQ = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
      have hnat : fQ.natDegree = 4 := by
        dsimp [fQ]
        compute_degree <;> norm_num
      rw [degree_eq_natDegree hfQ_ne, hnat] at hdeg
      norm_num at hdeg
    · intro a b hab
      have ha_ne : a ≠ 0 := by
        intro ha
        rw [ha, zero_mul] at hab
        exact hfQ_ne hab
      have hb_ne : b ≠ 0 := by
        intro hb
        rw [hb, mul_zero] at hab
        exact hfQ_ne hab
      by_cases ha_pos : 0 < degree a
      · right
        apply Polynomial.isUnit_iff_degree_eq_zero.mpr
        apply le_antisymm
        · apply le_of_not_gt
          intro hb_pos
          exact h_no_factor ⟨a, b, hab.symm, ha_pos, hb_pos⟩
        · rw [degree_eq_natDegree hb_ne]
          simp
      · left
        apply Polynomial.isUnit_iff_degree_eq_zero.mpr
        apply le_antisymm
        · exact le_of_not_gt ha_pos
        · rw [degree_eq_natDegree ha_ne]
          simp
  have hmonic : (X^4 - 4*X^3 + 6 : ℤ[X]).Monic := by
    monicity <;> norm_num
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mpr
  simpa [fQ] using hfQ_irred
