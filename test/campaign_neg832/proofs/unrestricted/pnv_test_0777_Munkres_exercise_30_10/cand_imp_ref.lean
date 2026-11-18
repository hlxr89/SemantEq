import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, Countable (X i)] (hX : ∀ i, ∃ D : Set (X i), Dense D) : ∃ D : Set (∀ i, X i), Dense D := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  letI : ∀ i, TopologicalSpace.SeparableSpace (X i) := fun i => ⟨h i⟩
  exact TopologicalSpace.exists_countable_dense (∀ i, X i)
