import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [LinearOrder α] {s : Set α} (h : s.Nonempty) (a : α) (ha : ∀ x ∈ s, a ≤ x) (b : α) (hb : ∀ x ∈ s, x ≤ b) : a ≤ b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_4
(α : Type*) [PartialOrder α]
(s : Set α)
(x y : α)
(h₀ : Set.Nonempty s)
(h₁ : x ∈ lowerBounds s)
(h₂ : y ∈ upperBounds s)
: x ≤ y := by
  obtain ⟨z, hz⟩ := h₀
  exact (h₁ hz).trans (h₂ hz)
