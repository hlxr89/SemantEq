import Mathlib

open Filter Topology Real Nat

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1995_b4_solution : ℤ × ℤ × ℤ × ℤ := ⟨3,1,5,2⟩

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  let x : ℝ := (2207 + Real.sqrt (2207^2 - 4)) / 2
  x ^ (1 / (8 : ℝ)) = (3 + Real.sqrt 5) / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1995_b4
    (contfrac : ℝ)
    (hcontfrac : contfrac = 2207 - 1 / contfrac)
    (hcontfrac' : 1 < contfrac) :
    let ⟨a, b, c, d⟩ := putnam_1995_b4_solution
    contfrac ^ ((1 : ℝ) / 8) = (a + b * sqrt c) / d := by
  have hne : contfrac ≠ 0 := ne_of_gt (lt_trans zero_lt_one hcontfrac')
  have hquad : contfrac ^ 2 - 2207 * contfrac + 1 = 0 := by
    field_simp [hne] at hcontfrac -- non-rewrite step
    nlinarith [hcontfrac] -- non-rewrite step
  have hsqrt : (Real.sqrt ((2207 : ℝ)^2 - 4)) ^ 2 = (2207 : ℝ)^2 - 4 := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((2207 : ℝ)^2 - 4) := Real.sqrt_nonneg _
  have hmul : 0 < (contfrac - 1) * (contfrac - 2206) := by
    nlinarith [hquad] -- non-rewrite step
  have hlarge : 2206 < contfrac := by
    exact sub_pos.mp (pos_of_mul_pos_right hmul (le_of_lt (sub_pos.mpr hcontfrac')))
  have hsq : (2 * contfrac - 2207) ^ 2 =
      (Real.sqrt ((2207 : ℝ)^2 - 4)) ^ 2 := by
    nlinarith [hquad, hsqrt] -- non-rewrite step
  have hlinear : 2 * contfrac - 2207 = Real.sqrt ((2207 : ℝ)^2 - 4) := by
    exact (sq_eq_sq₀ (by nlinarith [hlarge]) hsqrt_nonneg).mp hsq
  have hroot : contfrac = (2207 + Real.sqrt ((2207 : ℝ)^2 - 4)) / 2 := by
    rw [eq_div_iff (by positivity : (2 : ℝ) ≠ 0)]
    nlinarith [hlinear] -- non-rewrite step
  rw [hroot]
  simpa only [putnam_1995_b4_solution, Int.cast_ofNat, Int.cast_one, one_mul] using
    problem_statement_assumed
