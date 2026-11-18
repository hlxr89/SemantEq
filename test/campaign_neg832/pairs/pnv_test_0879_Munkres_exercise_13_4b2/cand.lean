import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : Type*} (T : ι → TopologicalSpace X) : ∃! (m : TopologicalSpace X), ∀ (i : ι), T i ≤ m := sorry
