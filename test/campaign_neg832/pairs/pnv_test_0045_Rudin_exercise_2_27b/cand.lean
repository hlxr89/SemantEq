import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {α : Type*} [TopologicalSpace α] [T2Space α] (E : Set α) (hE : Uncountable E) (P : Set α) : Set.Countable {x : α | x ∈ E \ P} := sorry
