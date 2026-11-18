import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] (f : ℕ → X) : IsClopen (Set.range f) := sorry
