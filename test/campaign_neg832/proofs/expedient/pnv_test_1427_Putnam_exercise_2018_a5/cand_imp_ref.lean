import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hf₂ : ∀ x, 0 ≤ f x) : ∃ n : ℕ, ∃ x : ℝ, f ^[n] x < 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_a5 (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : ∀ x, f x ≥ 0) :
  ∃ (n : ℕ+) (x : ℝ), iteratedDeriv n f x < 0 := by
  by_contra h
  push_neg at h
  have hderiv : ∀ x, 0 ≤ deriv f x := by
    intro x
    simpa only [show ((1 : ℕ+) : ℕ) = 1 by rfl, iteratedDeriv_one] using h (1 : ℕ+) x
  have hmono : Monotone f :=
    monotone_of_deriv_nonneg (hf.differentiable (by simp)) hderiv
  have hzero : ∀ x ≤ 0, f x = 0 := by
    intro x hx
    apply le_antisymm
    · simpa only [hf0] using hmono hx
    · exact hf2 x
  have hev : f =ᶠ[nhds (-1 : ℝ)] (fun _ ↦ 0) := by
    filter_upwards [eventually_lt_nhds (show (-1 : ℝ) < 0 by norm_num)] with x hx
    exact hzero x hx.le
  have heq : f = fun _ : ℝ ↦ 0 :=
    (hf.analyticOnNhd (s := Set.univ)).eq_of_eventuallyEq analyticOnNhd_const hev
  have := congrFun heq 1
  simp only [hf1] at this
  norm_num at this
