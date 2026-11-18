import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f g : X → Y} {E : Set X} (hE : Dense E) (hfg : ∀ p ∈ E, f p = g p) : ∀ x : X, f x = g x := by
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
  funext x
  have h := dummy_assumed (Y := UniformSpace.Completion β) h₃
    (fun p hp => congrArg (fun y : β => (y : UniformSpace.Completion β)) (h₄ p hp)) x
  exact (UniformSpace.Completion.coe_injective β) h
