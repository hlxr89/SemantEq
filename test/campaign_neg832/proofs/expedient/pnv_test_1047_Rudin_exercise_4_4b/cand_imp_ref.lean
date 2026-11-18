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
  exfalso
  let u : ℝ → ℝ := fun y => if y = 0 then 1 else 0
  have hu : ContinuousAt u 0 :=
    (dummy_assumed (f := u) (g := u) (x := 0)).mp (Filter.Eventually.of_forall fun _ => rfl) |>.1
  rw [Metric.continuousAt_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu (1 / 2) (by norm_num)
  have hx0 : δ / 2 ≠ 0 := by positivity
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq]
    have hd2 : 0 < δ / 2 := by linarith
    rw [sub_zero, abs_of_pos hd2]
    linarith
  have := hδ' hdist
  simp [u, hx0] at this
  norm_num at this
