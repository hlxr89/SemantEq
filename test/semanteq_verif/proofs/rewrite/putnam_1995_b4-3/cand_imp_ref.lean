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
    contfrac ^ ((1 : ℝ) / 8) = (a + b * sqrt c) / d := by
  have hcontfrac_pos : 0 < contfrac := lt_trans (by norm_num) hcontfrac' -- non-rewrite step
  have hinv_lt : 1 / contfrac < 1 := (div_lt_one hcontfrac_pos).2 hcontfrac'
  have hcontfrac_large : 2206 < contfrac := by
    rw [hcontfrac]
    linarith -- non-rewrite step
  have hquad : contfrac ^ 2 - 2207 * contfrac + 1 = 0 := by
    have h := hcontfrac
    field_simp [ne_of_gt hcontfrac_pos] at h -- non-rewrite step
    nlinarith [h] -- non-rewrite step
  have hdisc : (0 : ℝ) ≤ 2207 ^ 2 - 4 := by
    norm_num -- non-rewrite step
  have hsqrt_sq : (Real.sqrt ((2207 : ℝ) ^ 2 - 4)) ^ 2 = 2207 ^ 2 - 4 :=
    Real.sq_sqrt hdisc
  have hcontfrac_eq : contfrac = nested_fraction := by
    rw [nested_fraction]
    have hsqrt_nonneg := Real.sqrt_nonneg ((2207 : ℝ) ^ 2 - 4)
    have hshift_pos : 0 < 2 * contfrac - 2207 := by
      linarith -- non-rewrite step
    have hshift_sq : (2 * contfrac - 2207) ^ 2 =
        (Real.sqrt ((2207 : ℝ) ^ 2 - 4)) ^ 2 := by
      nlinarith [hquad, hsqrt_sq] -- non-rewrite step
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hshift_sq with hshift | hshift
    · apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2 -- non-rewrite step
      linarith -- non-rewrite step
    · exfalso
      linarith -- non-rewrite step
  rw [hcontfrac_eq]
  have hcand := problem_statement_assumed
  rw [Real.rpow_eq_pow] at hcand
  convert hcand using 1 <;> norm_num [putnam_1995_b4_solution] -- non-rewrite step
