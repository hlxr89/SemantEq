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
  have hrootx : x ^ (1 / 8 : ℝ) = (3 + Real.sqrt 5) / 2 := by
    rw [hx]
    exact hroot
  have hrootgt : 1 < x ^ (1 / 8 : ℝ) := by
    rw [hrootx]
    linarith only [Real.sqrt_nonneg 5]
  have hxgt : 1 < x := by
    exact (Real.rpow_lt_rpow_iff (x := 1) (y := x) (z := (1 / 8 : ℝ))
      (by positivity) hxpos.le (by positivity)).mp
      (by simpa only [Real.one_rpow] using hrootgt)
  have hcne : contfrac ≠ 0 := ne_of_gt (lt_trans (by positivity) hcontfrac')
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hcdiv : 1 / contfrac = 2207 - contfrac := by
    linarith only [hcontfrac]
  have hxdiv : 1 / x = 2207 - x := by
    linarith only [hx]
  have hcprod : (1 : ℝ) = (2207 - contfrac) * contfrac :=
    (div_eq_iff hcne).mp hcdiv
  have hxprod : (1 : ℝ) = (2207 - x) * x :=
    (div_eq_iff hxne).mp hxdiv
  have hcx : contfrac = x := by
    nlinarith [mul_pos (sub_pos.mpr hcontfrac') (sub_pos.mpr hxgt)] -- non-rewrite step: uniqueness above one.
  rw [hcx]
  simpa [putnam_1995_b4_solution] using hrootx
