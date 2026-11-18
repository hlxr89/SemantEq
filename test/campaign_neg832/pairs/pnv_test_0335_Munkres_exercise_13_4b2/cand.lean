import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type u} {ι : Type v} (F : ι → TopologicalSpace X) : ∃! T : TopologicalSpace X, ∀ i, T ≤ F i := sorry
