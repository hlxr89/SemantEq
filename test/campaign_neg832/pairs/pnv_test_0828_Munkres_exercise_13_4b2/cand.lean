import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (X : Type u) (T : ι → TopologicalSpace X) : ∃ (m : TopologicalSpace X), (∀ i, T i ≤ m) ∧ ∀ (t : TopologicalSpace X) (h : ∀ i, T i ≤ t), m ≤ t := sorry
