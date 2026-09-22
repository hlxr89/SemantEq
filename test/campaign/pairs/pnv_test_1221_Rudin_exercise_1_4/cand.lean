import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {α : Type*} [PartialOrder α] {s : Set α} (hs : s.Nonempty) {a b : α} (ha : ∀ x ∈ s, a ≤ x) (hb : ∀ x ∈ s, x < b) : a ≤ b := sorry
