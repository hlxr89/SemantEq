import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {K : Type*} [MetricSpace K] [CompactSpace K] : ∃ B : Set (Set K), Countable B ∧ TopologicalSpace.IsTopologicalBasis B := sorry
