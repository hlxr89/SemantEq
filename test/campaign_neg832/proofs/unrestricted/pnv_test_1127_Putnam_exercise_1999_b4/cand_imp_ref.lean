import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ x : ℝ, HasDerivAt f (deriv f x) x) (hdf : ∀ x : ℝ, HasDerivAt (deriv f) (deriv (deriv f) x) x) (hg : ∀ x : ℝ, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x) (hgf : ∀ x : ℝ, (deriv f x) > 0) (hg2f : ∀ x : ℝ, (deriv (deriv f) x) > 0) (hg2gf : ∀ x : ℝ, (deriv (deriv (deriv f)) x) ≤ (deriv f x)) : ∀ x : ℝ, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  exfalso
  let g : ℝ → ℝ := fun x => Real.exp x - 1
  have hg_deriv : deriv g = Real.exp := by
    funext x
    exact (Real.hasDerivAt_exp x).sub_const 1 |>.deriv
  have hfalse := dummy_assumed g
    (fun x => by simpa [g, hg_deriv] using (Real.hasDerivAt_exp x).sub_const 1)
    (fun x => by simpa [hg_deriv] using Real.hasDerivAt_exp x)
    (fun x => by simpa [hg_deriv] using Real.hasDerivAt_exp x)
    (fun x => by simpa [hg_deriv] using Real.exp_pos x)
    (fun x => by simpa [hg_deriv] using Real.exp_pos x)
    (fun x => by simp [hg_deriv])
  have := hfalse 0
  norm_num [g, hg_deriv] at this
