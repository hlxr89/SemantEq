import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] : ∃ (B : ℕ → Set X), (∀ n, IsOpen (B n)) ∧ (∀ x : X, ∃ n : ℕ, x ∈ B n) ∧ ∀ (x : X) (U : Set X), x ∈ U ∧ IsOpen U → ∃ (n : ℕ), B n ⊆ U := sorry
