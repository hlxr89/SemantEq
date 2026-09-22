import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y} {E : Set X} (hf : Continuous f) (hg : Continuous g) (hE : Dense E) (he : ∀ p ∈ E, g p = f p) : ∀ p, g p = f p := by
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
  funext p
  exact dummy_assumed (f := g) (g := f) h₂ h₁ h₃ h₄ p
