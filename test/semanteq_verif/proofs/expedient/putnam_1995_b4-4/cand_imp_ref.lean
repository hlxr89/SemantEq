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
  have hcpos : 0 < contfrac := lt_trans (by norm_num) hcontfrac'
  have hxone : 1 < x := by
    rw [← hx] at hroot
    by_contra h
    have hle : x ^ ((1 : ℝ) / 8) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hxpos) (le_of_not_gt h) (by norm_num)
    rw [hroot] at hle
    nlinarith [Real.sqrt_nonneg 5]
  have hcx : contfrac = x := by
    have hc0 : contfrac ≠ 0 := ne_of_gt hcpos
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    field_simp [hc0] at hcontfrac
    field_simp [hx0] at hx
    have hp : (contfrac - x) * (contfrac + x - 2207) = 0 := by
      nlinarith [hcontfrac, hx]
    rcases mul_eq_zero.mp hp with h | h
    · linarith
    · have hxeq : x = 2207 - contfrac := by linarith
      have hprod : contfrac * x = 1 := by
        rw [hxeq]
        nlinarith [hcontfrac]
      have : 1 < contfrac * x := by
        nlinarith [mul_pos (sub_pos.mpr hcontfrac') (sub_pos.mpr hxone)]
      linarith
  dsimp [putnam_1995_b4_solution]
  rw [hcx, hx]
  norm_num
  simpa [div_eq_mul_inv] using hroot
