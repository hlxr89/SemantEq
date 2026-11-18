import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f g : ℝ → ℝ} {x : ℝ} (f' : ℝ → ℝ) (g' : ℝ → ℝ) (hx : f x = g x) (hf' : HasDerivAt f (f' x) x) (hg' : HasDerivAt g (g' x) x) (hg'0 : g' x ≠ 0) : HasDerivAt (fun x => f x / g x) ((f' x * g x - f x * g' x) / g' x ^ 2) x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_7
  {f g : ℝ → ℝ} {x : ℝ}
  (hf' : DifferentiableAt ℝ f x)
  (hg' : DifferentiableAt ℝ g x)
  (hg'_ne_0 : deriv g x ≠ 0)
  (f0 : f x = 0) (g0 : g x = 0) :
  Tendsto (λ t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x)) := by
  exfalso
  have hc := dummy_assumed
    (f := fun t : ℝ => t) (g := fun t : ℝ => 2 * t - 1) (x := 1)
    (fun _ => 1) (fun _ => 2) (by norm_num)
    (by simpa using hasDerivAt_id (𝕜 := ℝ) (1 : ℝ))
    (by simpa using ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).const_mul 2).sub_const 1)
    (by norm_num)
  have hg : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 1 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).const_mul 2).sub_const 1
  have ha := (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).div hg (by norm_num)
  have := hc.unique ha
  norm_num at this
