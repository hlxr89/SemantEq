import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] : ∃ B : ℕ → Set X, ∀ (x : X), ∃ n, x ∈ closure (B n) ∧ ∀ m, m ≤ n → closure (B m) ⊆ closure (B n) := sorry
