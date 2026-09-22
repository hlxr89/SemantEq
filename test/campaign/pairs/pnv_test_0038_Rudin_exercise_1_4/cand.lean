import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {α : Type u} [PartialOrder α] {E : Set α} {a b : α} (ha : IsLUB E a) (hb : IsGLB E b) : a ≤ b := sorry
