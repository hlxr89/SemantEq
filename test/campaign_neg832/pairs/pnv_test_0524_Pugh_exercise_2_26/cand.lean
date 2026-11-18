import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [TopologicalSpace M] (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ∀ (V : Set M), IsOpen V → x ∈ V → (V ∩ Uᶜ).Nonempty → False := sorry
