import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (E : Set ℝ) (f : ℝ → ℝ) (h : ContinuousOn f E) : ∃ (g : ℝ → ℝ), ContinuousOn g E ∧ ∀ (x : ℝ), g x = f x → (x ∈ E ∨ ¬ ContinuousAt g x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  refine ⟨Set.Ioi 0, fun x : ℝ => x⁻¹, ?_, ?_⟩
  · exact continuousOn_id.inv₀ (fun x hx => ne_of_gt hx)
  · rintro ⟨g, hg, hagree⟩
    let u : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
    have hu : Tendsto u atTop (𝓝 0) := by
      simpa [u] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hgu : Tendsto (fun n => g (u n)) atTop (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.comp hu
    have heq : (fun n => g (u n)) = fun n : ℕ => ((n + 1 : ℕ) : ℝ) := by
      funext n
      rw [← hagree (u n) (by
        show 0 < (((n + 1 : ℕ) : ℝ)⁻¹)
        positivity)]
      simp [u]
    have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact (not_tendsto_nhds_of_tendsto_atTop htop (g 0)) (heq ▸ hgu)
