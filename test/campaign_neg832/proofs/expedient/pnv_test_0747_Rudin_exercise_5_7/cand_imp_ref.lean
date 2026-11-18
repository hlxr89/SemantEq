import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [LinearOrder X] [OrderTopology X] {f g : ℝ → ℝ} {a : ℝ} (f' : ℝ → ℝ) (g' : ℝ → ℝ) (hff' : ∀ x ≠ a, HasDerivAt f (f' x) x) (hg' : ∀ x ≠ a, HasDerivAt g (g' x) x) (hfa : f a = 0) (hga : g a = 0) (hg'_ne : ∀ x ≠ a, g' x ≠ 0) : Tendsto (fun t => (f t) / (g t)) (𝓝 a) (𝓝 (f' a / g' a)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_7
  {f g : ℝ → ℝ} {x : ℝ}
  (hf' : DifferentiableAt ℝ f x)
  (hg' : DifferentiableAt ℝ g x)
  (hg'_ne_0 : deriv g x ≠ 0)
  (f0 : f x = 0) (g0 : g x = 0) :
  Tendsto (λ t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x)) := by
  let f' : ℝ → ℝ := fun y => if y = 0 then 1 else 0
  have hbad : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 1) := by
    simpa [f'] using
      (dummy_assumed (X := ℝ) (f := fun _ => 0) (g := fun y => y) (a := 0)
        f' (fun _ => 1)
        (by
          intro y hy
          simpa [f', hy] using (hasDerivAt_const (x := y) (c := (0 : ℝ))))
        (by
          intro y hy
          simpa using (hasDerivAt_id y))
        (by simp) (by simp) (by simp))
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0) := tendsto_const_nhds
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hbad
  norm_num at this
