import Mathlib

open Filter Topology Real Nat

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1995_b4_solution : ℤ × ℤ × ℤ × ℤ := ⟨3,1,5,2⟩

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∃ (x : ℝ), 
    x = 2207 - 1/x ∧ 
    x > 0 ∧
    (2207 - 1/x)^(1/8 : ℝ) = (3 + Real.sqrt 5) / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1995_b4
    (contfrac : ℝ)
    (hcontfrac : contfrac = 2207 - 1 / contfrac)
    (hcontfrac' : 1 < contfrac) :
    let ⟨a, b, c, d⟩ := putnam_1995_b4_solution
    contfrac ^ ((1 : ℝ) / 8) = (a + b * sqrt c) / d := by
  obtain ⟨x, hx, hxpos, hroot⟩ := problem_statement_assumed
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hcpos : 0 < contfrac := lt_trans (by norm_num) hcontfrac'
  have hcne : contfrac ≠ 0 := ne_of_gt hcpos
  have hxquad : x ^ 2 = 2207 * x - 1 := by
    field_simp [hxne] at hx
    nlinarith
  have hcquad : contfrac ^ 2 = 2207 * contfrac - 1 := by
    field_simp [hcne] at hcontfrac
    nlinarith
  have hrootx : x ^ (1 / 8 : ℝ) = (3 + Real.sqrt 5) / 2 := by
    rw [hx]
    exact hroot
  have hxone : 1 < x := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    by_contra h
    have hxle : x ≤ 1 := le_of_not_gt h
    have hrpow_le : x ^ (1 / 8 : ℝ) ≤ 1 :=
      Real.rpow_le_one hxpos.le hxle (by norm_num)
    rw [hrootx] at hrpow_le
    nlinarith
  have hxeq : x = contfrac := by
    have hfactor : (x - contfrac) * (x + contfrac - 2207) = 0 := by
      nlinarith [hxquad, hcquad]
    rcases mul_eq_zero.mp hfactor with hsame | hsum
    · linarith
    · have hprod_x : x * (2207 - x) = 1 := by nlinarith [hxquad]
      have hprod : x * contfrac = 1 := by nlinarith [hprod_x]
      have hm : 0 < (x - 1) * (contfrac - 1) :=
        mul_pos (sub_pos.mpr hxone) (sub_pos.mpr hcontfrac')
      nlinarith
  dsimp [putnam_1995_b4_solution]
  rw [← hxeq]
  simpa using hrootx
