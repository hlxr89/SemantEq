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
  let g : ℝ → ℝ := fun x => Real.exp x - 1
  have hd : ∀ x : ℝ, deriv g x = Real.exp x := by
    intro x
    simpa [g] using Real.hasDerivAt_exp x |>.deriv
  have hdd : ∀ x : ℝ, deriv (deriv g) x = Real.exp x := by
    simp only [funext hd]
    exact fun x => Real.hasDerivAt_exp x |>.deriv
  have hddd : ∀ x : ℝ, deriv (deriv (deriv g)) x = Real.exp x := by
    simp only [funext hdd]
    exact fun x => Real.hasDerivAt_exp x |>.deriv
  have bad := dummy_assumed g
    (fun x => by rw [hd x]; exact (Real.hasDerivAt_exp x).sub_const 1)
    (fun x => by rw [hdd x, funext hd]; exact Real.hasDerivAt_exp x)
    (fun x => by rw [hddd x, funext hdd]; exact Real.hasDerivAt_exp x)
    (fun x => by rw [hd]; exact Real.exp_pos x)
    (fun x => by rw [hdd]; exact Real.exp_pos x)
    (fun x => by rw [hddd, hd])
  have := bad 0
  norm_num [g, hd] at this
