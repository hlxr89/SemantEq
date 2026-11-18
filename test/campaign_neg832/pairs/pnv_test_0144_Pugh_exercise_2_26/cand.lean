import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [TopologicalSpace M] {U : Set M} : IsOpen U ↔ ∀ (x : M), x ∉ U → x ∉ closure (Set.compl U) := sorry
