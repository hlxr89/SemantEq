import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] (S : Set X) : (IsOpen S ∧ IsClosed S) ↔ IsClopen S := sorry
