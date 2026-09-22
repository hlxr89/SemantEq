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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X) (hE : Dense E) (f g : X → Y) (hf : Continuous f) (hg : Continuous g) (hfg : ∀ (p : X), p ∈ E → g p = f p) : ∀ (p : X), g p = f p := by
  intro p
  exact congrFun (hg.ext_on hE hf hfg) p
