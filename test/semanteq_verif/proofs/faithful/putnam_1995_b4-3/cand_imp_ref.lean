import Mathlib

open Filter Topology Real Nat

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1995_b4_solution : ℤ × ℤ × ℤ × ℤ := ⟨3,1,5,2⟩

noncomputable def nested_fraction : ℝ := (2207 + Real.sqrt (2207^2 - 4)) / 2

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : Real.rpow nested_fraction (1/8) = (3 + Real.sqrt 5) / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1995_b4
    (contfrac : ℝ)
    (hcontfrac : contfrac = 2207 - 1 / contfrac)
    (hcontfrac' : 1 < contfrac) :
    let ⟨a, b, c, d⟩ := putnam_1995_b4_solution
    contfrac ^ ((1 : ℝ) / 8) = (a + b * sqrt c) / d :=
  by
    have hcontfrac_pos : 0 < contfrac := lt_trans (by norm_num) hcontfrac'
    have hcontfrac_ne : contfrac ≠ 0 := ne_of_gt hcontfrac_pos
    have hinv_lt : 1 / contfrac < 1 := (div_lt_one hcontfrac_pos).2 hcontfrac'
    have hlarge : 2206 < contfrac := by nlinarith [hcontfrac]
    have hquad : contfrac ^ 2 - 2207 * contfrac + 1 = 0 := by
      field_simp [hcontfrac_ne] at hcontfrac
      nlinarith [hcontfrac]
    have hdisc : (0 : ℝ) ≤ 2207 ^ 2 - 4 := by norm_num
    have hsqrt_sq : (Real.sqrt (2207 ^ 2 - 4)) ^ 2 = (2207 : ℝ) ^ 2 - 4 := by
      rw [Real.sq_sqrt hdisc]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2207 ^ 2 - 4) := Real.sqrt_nonneg _
    have hroot_sq : (2 * contfrac - 2207) ^ 2 = (Real.sqrt (2207 ^ 2 - 4)) ^ 2 := by
      nlinarith [hquad, hsqrt_sq]
    have hroot_nonneg : 0 ≤ 2 * contfrac - 2207 := by nlinarith [hlarge]
    have hroot : 2 * contfrac - 2207 = Real.sqrt (2207 ^ 2 - 4) := by
      nlinarith [hroot_sq, hroot_nonneg, hsqrt_nonneg]
    have hident : contfrac = nested_fraction := by
      rw [nested_fraction]
      field_simp
      nlinarith [hroot]
    simpa [putnam_1995_b4_solution, hident] using problem_statement_assumed
