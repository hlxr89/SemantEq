import Mathlib

open Filter Topology Real Nat
open Real

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1995_b4_solution : ℤ × ℤ × ℤ × ℤ := ⟨3,1,5,2⟩

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ((2207 + Real.sqrt (2207^2 - 4)) / 2) ^ (1/8 : ℝ) = (3 + Real.sqrt 5) / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1995_b4
    (contfrac : ℝ)
    (hcontfrac : contfrac = 2207 - 1 / contfrac)
    (hcontfrac' : 1 < contfrac) :
    let ⟨a, b, c, d⟩ := putnam_1995_b4_solution
    contfrac ^ ((1 : ℝ) / 8) = (a + b * sqrt c) / d := by
  have hpos : 0 < contfrac := lt_trans zero_lt_one hcontfrac'
  have hne : contfrac ≠ 0 := ne_of_gt hpos
  have hmul : contfrac * contfrac = (2207 - 1 / contfrac) * contfrac := by
    rw [← hcontfrac]
  rw [sub_mul, div_mul_cancel₀ 1 hne] at hmul
  have hplus : contfrac * contfrac + 1 = 2207 * contfrac :=
    eq_sub_iff_add_eq.mp hmul
  have hquad : (1 : ℝ) * (contfrac * contfrac) + (-2207) * contfrac + 1 = 0 := by
    linarith [hplus] -- non-rewrite step
  have hs : Real.sqrt (2207 ^ 2 - 4) * Real.sqrt (2207 ^ 2 - 4) =
      (2207 : ℝ) ^ 2 - 4 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  have hdisc : discrim (1 : ℝ) (-2207) 1 =
      Real.sqrt (2207 ^ 2 - 4) * Real.sqrt (2207 ^ 2 - 4) := by
    simpa only [discrim, neg_sq, one_mul, mul_one] using hs.symm
  have hroots := (quadratic_eq_zero_iff (a := (1 : ℝ)) (b := -2207) (c := 1)
    one_ne_zero hdisc contfrac).mp hquad
  have hinv : 1 / contfrac < 1 := by
    simpa only [div_one] using
      (one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := contfrac) zero_lt_one hcontfrac')
  have hlarge : 2206 < contfrac := by
    linarith [hcontfrac] -- non-rewrite step
  have hroot : contfrac = (2207 + Real.sqrt (2207 ^ 2 - 4)) / 2 := by
    rcases hroots with hroot | hroot
    · simpa only [neg_neg, one_mul, mul_one] using hroot
    · exfalso
      have hsnonneg := Real.sqrt_nonneg (2207 ^ 2 - 4)
      simp only [neg_neg, mul_one] at hroot
      have hroot' := (eq_div_iff (by positivity : (2 : ℝ) ≠ 0)).mp hroot
      linarith -- non-rewrite step
  rw [hroot]
  simpa only [putnam_1995_b4_solution, Int.cast_ofNat, Int.cast_one, one_mul] using
    problem_statement_assumed
