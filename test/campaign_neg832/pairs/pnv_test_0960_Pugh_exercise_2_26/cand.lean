import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {X : Type u} [TopologicalSpace X] (U : Set X) : IsOpen U ↔ ∀ x : X, x ∈ U → ¬ x ∈ closure (Uᶜ) := sorry
