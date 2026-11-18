import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ x, f x > 0) (hf' : ∀ x, HasDerivAt f (f x) x) (hf'' : ∀ x, HasDerivAt (deriv f) (deriv f x) x) (hf''' : ∀ x, HasDerivAt (deriv (deriv f)) (deriv (deriv f) x) x) (h : ∀ x, (deriv (deriv (deriv f))) x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  intro x
  have hcd1 : ContDiff ℝ 3 (fun t : ℝ => f (x - t)) := hf.comp (by fun_prop)
  obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) (x₀ := (0 : ℝ)) (x := 1) (by norm_num) hcd1.contDiffOn
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hd1 := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
    (hcd1.contDiffAt.of_le (by norm_num)) (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  have hd2 := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu
    (hcd1.contDiffAt.of_le (by norm_num)) (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval, hd1, hd2] at he
  rw [iteratedDeriv_comp_const_sub 1 f x, iteratedDeriv_comp_const_sub 2 f x,
    iteratedDeriv_comp_const_sub 3 f x] at he
  norm_num [iteratedDeriv_succ] at he
  have hp0 := hf1 0 (by norm_num) (x - 1)
  have hp3 := hf1 3 (by norm_num) (x - c)
  norm_num [iteratedDeriv_succ] at hp0 hp3
  have hA : deriv f x < f x + deriv (deriv f) x / 2 := by linarith
  have hfd : ContDiff ℝ 2 (deriv f) := by exact hf.deriv'
  have hcd2 : ContDiff ℝ 2 (fun t : ℝ => deriv f (x - t)) := hfd.comp (by fun_prop)
  obtain ⟨d, hd, he'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (x₀ := (0 : ℝ)) (x := 2) (by norm_num) hcd2.contDiffOn
  have hu' : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 2) := uniqueDiffOn_Icc (by norm_num)
  have hde := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu'
    (hcd2.contDiffAt.of_le (by norm_num)) (show (0 : ℝ) ∈ Set.Icc 0 2 by norm_num)
  rw [taylorWithinEval_succ, taylor_within_zero_eval, hde] at he'
  rw [iteratedDeriv_comp_const_sub 1 (deriv f) x,
    iteratedDeriv_comp_const_sub 2 (deriv f) x] at he'
  norm_num [iteratedDeriv_succ] at he'
  have hp1back := hf1 1 (by norm_num) (x - 2)
  norm_num [iteratedDeriv_succ] at hp1back
  have hmono : StrictMono f := strictMono_of_deriv_pos (by
    intro y
    simpa [iteratedDeriv_succ] using hf1 1 (by norm_num) y)
  have hdx : x - d < x := by linarith [hd.1]
  have hbound := hf2 (x - d)
  norm_num [iteratedDeriv_succ] at hbound
  have hB : deriv (deriv f) x < deriv f x / 2 + f x := by
    have := hmono hdx
    linarith
  linarith
