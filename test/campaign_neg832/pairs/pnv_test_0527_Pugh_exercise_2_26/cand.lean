import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [TopologicalSpace M] {U : Set M} : IsOpen U ↔ ∀ (x : M), ¬ x ∈ U → ∀ (V : Set M), IsOpen V → x ∈ closure ((U : Set M)ᶜ) → x ∈ V → False := sorry
