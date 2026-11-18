import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy [TopologicalSpace α] (s : Set α) : IsOpen s ↔ ∀ x ∈ s, ¬ x ∈ closure (sᶜ) := sorry
