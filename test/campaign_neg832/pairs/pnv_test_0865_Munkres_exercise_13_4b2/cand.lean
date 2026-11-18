import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (Tα : ι → TopologicalSpace X) : ∃ (T : TopologicalSpace X), ∀ (α : ι), Tα α ≤ T := sorry
