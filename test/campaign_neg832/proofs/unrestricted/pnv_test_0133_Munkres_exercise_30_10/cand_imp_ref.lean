import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} [Fintype ι] {X : ι → Type*} [Nonempty ι] [∀ i, TopologicalSpace (X i)] (hX : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) : ∃ (s : Set (∀ i, X i)), Countable s ∧ Dense s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  letI : ∀ i, SeparableSpace (X i) := fun i => ⟨h i⟩
  exact exists_countable_dense (Π i, X i)
