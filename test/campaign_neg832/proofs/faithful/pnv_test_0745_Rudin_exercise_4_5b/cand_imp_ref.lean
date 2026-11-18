import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (E : Set ℝ) (f : ℝ → ℝ) (h : ContinuousOn f E) : ∃ (g : ℝ → ℝ), ContinuousOn g E ∧ ∀ (x : ℝ), g x = f x → (x ∈ E ∨ ¬ ContinuousAt g x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  classical
  obtain ⟨g₀, hg₀, hprop₀⟩ := dummy_assumed Set.univ (fun _ : ℝ => 0) continuousOn_const
  have hg₀' : Continuous g₀ := continuousOn_univ.mp hg₀
  refine ⟨{0}ᶜ, (fun x : ℝ => x⁻¹ + g₀ x), ?_, ?_⟩
  · exact (continuousOn_inv₀ : ContinuousOn (fun x : ℝ => x⁻¹) {0}ᶜ).add hg₀'.continuousOn
  · rintro ⟨g, hg, hmatch⟩
    have heq : (fun x : ℝ => x⁻¹) =ᶠ[𝓝[≠] 0] (fun x => g x - g₀ x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have := hmatch x hx
      linarith
    have hg_lim : Tendsto (fun x => g x - g₀ x) (𝓝[≠] 0) (𝓝 (g 0 - g₀ 0)) :=
      (hg.sub hg₀').continuousAt.tendsto.mono_left inf_le_left
    have hinv_lim : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (𝓝 (g 0 - g₀ 0)) :=
      hg_lim.congr' heq.symm
    exact (not_tendsto_atTop_of_tendsto_nhds hinv_lim.norm)
      tendsto_norm_inv_nhdsNE_zero_atTop
