import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [T2Space X] (hX : Countable X) (B : ℕ → Set X) (hB : ∀ n, IsOpen (B n)) (hB' : ∀ x, ∃ n, x ∈ B n) (hB'' : ∀ n, Dense (B n)) : ∃ D : Set X, Countable D ∧ Dense D := sorry
