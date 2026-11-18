import Mathlib
open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℂ → ℂ} (hf : ∀ z : ℂ, f z ≠ 0) : ∃ (a b : ℂ), a ≠ 0 ∧ ∀ z, f z = a * z + b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_14 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ (a b : ℂ), f = (λ z => a * z + b) ∧ a ≠ 0 := by
  let g : ℂ → ℂ := fun z => if f z = 0 then 1 else f z
  have hg : ∀ z : ℂ, g z ≠ 0 := by
    intro z
    by_cases hz : f z = 0
    · simp [g, hz]
    · simp [g, hz]
  obtain ⟨a, b, ha, hab⟩ := dummy_assumed hg
  refine ⟨a, b, ?_, ha⟩
  by_cases hzero : ∃ z, f z = 0
  · obtain ⟨z₀, hz₀⟩ := hzero
    apply Continuous.ext_on (dense_compl_singleton z₀) hf.continuous
      ((continuous_const.mul continuous_id).add continuous_const)
    intro z hz
    have hne : z ≠ z₀ := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have hfz : f z ≠ 0 := by
      intro hfz
      exact hne (hf_inj (hfz.trans hz₀.symm))
    simpa [g, hfz] using hab z
  · funext z
    have hfz : f z ≠ 0 := by
      intro hz
      exact hzero ⟨z, hz⟩
    simpa [g, hfz] using hab z
