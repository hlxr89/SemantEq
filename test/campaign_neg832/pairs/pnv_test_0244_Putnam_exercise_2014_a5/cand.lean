import Mathlib

open scoped BigOperators

theorem dummy {α : Type*} {s t : Set α} {x : α} (h : x ∈ s ∪ t) : x ∈ s ∧ x ∉ t ∨ x ∉ s ∧ x ∈ t := sorry
