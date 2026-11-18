import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (X : Type u) (α : Type v) (Tα : α → TopologicalSpace X) : ∃! (T : TopologicalSpace X), ∀ (a : α), Tα a ≤ T := sorry
