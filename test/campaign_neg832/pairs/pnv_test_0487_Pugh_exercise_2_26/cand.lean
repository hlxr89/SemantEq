import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {α : Type u} [TopologicalSpace α] {s : Set α} : IsOpen s ↔ ∀ x ∈ s, s ∈ nhds x := sorry
