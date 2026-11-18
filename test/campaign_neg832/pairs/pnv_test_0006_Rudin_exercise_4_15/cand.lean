import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) (hf_nonneg : ∀ x : X, 0 ≤ f x) (hX : CompactSpace X) : ∃ x₀ : X, ∀ x : X, f x ≤ f x₀ := sorry
