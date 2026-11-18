import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4b_assumed
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x)
  : f = g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f g : X → Y} {x : X} : f =ᶠ[𝓝 x] g ↔ ContinuousAt f x ∧ g =ᶠ[𝓝 x] f := by
  -- not proved: the candidate statement is false for discontinuous f with g = f
  sorry
