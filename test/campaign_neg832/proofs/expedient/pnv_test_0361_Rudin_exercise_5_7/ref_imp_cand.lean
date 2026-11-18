import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_7_assumed
  {f g : ℝ → ℝ} {x : ℝ}
  (hf' : DifferentiableAt ℝ f x)
  (hg' : DifferentiableAt ℝ g x)
  (hg'_ne_0 : deriv g x ≠ 0)
  (f0 : f x = 0) (g0 : g x = 0) :
  Tendsto (λ t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f g : ℝ → ℝ} {x : ℝ} (f' : ℝ → ℝ) (g' : ℝ → ℝ) (hx : f x = g x) (hf' : HasDerivAt f (f' x) x) (hg' : HasDerivAt g (g' x) x) (hg'0 : g' x ≠ 0) : HasDerivAt (fun x => f x / g x) ((f' x * g x - f x * g' x) / g' x ^ 2) x := by
  exfalso
  have h : Tendsto (fun t : ℝ => t / t) (𝓝 0) (𝓝 1) := by
    simpa using exercise_5_7_assumed
      (f := fun t : ℝ => t) (g := fun t : ℝ => t) (x := 0)
      differentiableAt_id differentiableAt_id (by simp) (by simp) (by simp)
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), t / t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) :=
    h.eventually (isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioo (1 / 2) (3 / 2)))
  have := hevent.self_of_nhds
  norm_num at this
