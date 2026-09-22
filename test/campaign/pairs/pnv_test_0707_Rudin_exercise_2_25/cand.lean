import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {K : Type*} [MetricSpace K] [CompactSpace K] : ∃ (b : Set (Set K)), b.Countable ∧ IsTopologicalBasis b := sorry
