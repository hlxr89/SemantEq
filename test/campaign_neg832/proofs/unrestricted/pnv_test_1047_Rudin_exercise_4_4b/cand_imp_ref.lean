import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f g : X → Y} {x : X} : f =ᶠ[𝓝 x] g ↔ ContinuousAt f x ∧ g =ᶠ[𝓝 x] f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4b
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x)
  : f = g := by
  let spike : ℝ → ℝ := fun y => if y = 0 then 1 else 0
  have hcontinuous : ContinuousAt spike 0 :=
    (dummy_assumed (f := spike) (g := spike) (x := (0 : ℝ))).mp Filter.EventuallyEq.rfl |>.1
  rw [Metric.continuousAt_iff] at hcontinuous
  rcases hcontinuous (1 / 2) (by norm_num) with ⟨δ, hδ, hclose⟩
  have hδ2_pos : 0 < δ / 2 := by positivity
  have hδ2_ne : δ / 2 ≠ 0 := ne_of_gt hδ2_pos
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ2_pos]
    linarith
  have := hclose hdist
  simp [spike, hδ2_ne] at this
  norm_num at this
