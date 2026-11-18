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
  have h := exercise_5_7_assumed
    (f := fun t : ℝ => t) (g := fun t : ℝ => t) (x := 0)
    (hasDerivAt_id 0).differentiableAt (hasDerivAt_id 0).differentiableAt
    (by simpa using (hasDerivAt_id 0).deriv_ne_zero) (by norm_num) (by norm_num)
  have h' : Tendsto (fun t : ℝ => t / t) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using h
  have hopen : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds (by norm_num)
  have hpre : {t : ℝ | t / t ∈ Set.Ioi (1 / 2 : ℝ)} ∈ 𝓝 (0 : ℝ) := by
    simpa using h' hopen
  have hz : (0 : ℝ) ∈ {t : ℝ | t / t ∈ Set.Ioi (1 / 2 : ℝ)} :=
    mem_of_mem_nhds hpre
  norm_num at hz
