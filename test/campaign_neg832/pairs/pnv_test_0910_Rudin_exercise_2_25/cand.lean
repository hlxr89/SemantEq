import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (K : Type*) [MetricSpace K] [CompactSpace K] : ∃ (T : Set (Set K)), T.Countable ∧ (∀ (x : K), ∃ (U : Set K), U ∈ T ∧ IsOpen U ∧ x ∈ U) ∧ (∀ (x : K) (y : K), ∃ (U : Set K), U ∈ T ∧ U ⊆ {x} ∧ y ∈ U) := sorry
