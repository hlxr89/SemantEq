import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ x : ℝ, HasDerivAt f (f x) x) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hf₂ : ∀ x, 0 ≤ f x) : ∃ (n : ℕ) (x : ℝ), 0 < n ∧ deriv^[n] f x < 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ+) (x : ℝ), iteratedDeriv n f x < 0 := by
  by_contra hneg
  push_neg at hneg
  have hderiv : ∀ x : ℝ, 0 ≤ deriv f x := by
    intro x
    simpa [iteratedDeriv_one] using hneg (1 : ℕ+) x
  have hmono : Monotone f :=
    monotone_of_deriv_nonneg (hf.differentiable (by simp)) hderiv
  have heq : f =ᶠ[nhds (-1 : ℝ)] (fun _ : ℝ => 0) := by
    filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact le_antisymm (by simpa [hf0] using hmono (le_of_lt hx)) (hf2 x)
  have hfzero : f = (fun _ : ℝ => 0) :=
    hf.analyticOnNhd.eq_of_eventuallyEq analyticOnNhd_const heq
  have := congrFun hfzero 1
  norm_num [hf1] at this
