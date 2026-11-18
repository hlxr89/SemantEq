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
    contfrac ^ ((1 : ℝ) / 8) = (a + b * sqrt c) / d :=
  by
    dsimp [putnam_1995_b4_solution]
    have hc0 : 0 < contfrac := lt_trans (by norm_num) hcontfrac'
    have hcne : contfrac ≠ 0 := ne_of_gt hc0
    have hinv0 : 0 < 1 / contfrac := one_div_pos.mpr hc0
    have hinv1 : 1 / contfrac < 1 := by
      rw [div_lt_iff₀ hc0]
      simpa using hcontfrac'
    have hc_big : 2206 < contfrac := by linarith [hcontfrac]
    have hquad : contfrac ^ 2 - 2207 * contfrac + 1 = 0 := by
      field_simp [hcne] at hcontfrac
      nlinarith [hcontfrac]
    have hs : (Real.sqrt ((2207 : ℝ)^2 - 4)) ^ 2 = (2207 : ℝ)^2 - 4 :=
      Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt ((2207 : ℝ)^2 - 4) := Real.sqrt_nonneg _
    have hdisc : (2 * contfrac - 2207) ^ 2 = (2207 : ℝ)^2 - 4 := by
      nlinarith [hquad]
    have hroot : 2 * contfrac - 2207 = Real.sqrt ((2207 : ℝ)^2 - 4) := by
      nlinarith [hdisc, hs]
    have hc : contfrac = ((2207 : ℝ) + Real.sqrt ((2207 : ℝ)^2 - 4)) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
      linarith [hroot]
    rw [hc]
    simpa using problem_statement_assumed
