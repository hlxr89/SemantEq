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
  have hf : HasDerivAt (fun t : ℝ => 3 * t - 2) 3 1 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 1).const_mul 3 |>.sub_const 2 using 1 <;> norm_num
  have hg : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 1 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 1).const_mul 2 |>.sub_const 1 using 1 <;> norm_num
  have hbad := dummy_assumed
    (f := fun t : ℝ => 3 * t - 2) (g := fun t : ℝ => 2 * t - 1) (x := 1)
    (fun _ => 3) (fun _ => 2) (by norm_num) hf hg (by norm_num)
  have hgood : HasDerivAt (fun t : ℝ => (3 * t - 2) / (2 * t - 1)) 1 1 := by
    convert hf.div hg (by norm_num) using 1 <;> norm_num
  have := hbad.unique hgood
  norm_num at this
