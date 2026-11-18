import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [RegularSpace X] (x y : X) : ∃ N₁ N₂ : Set X, x ∈ N₁ ∧ y ∈ N₂ ∧ IsOpen N₁ ∧ IsOpen N₂ ∧ IsClosed (closure N₁) ∧ IsClosed (closure N₂) ∧ Disjoint (closure N₁) (closure N₂) := sorry
