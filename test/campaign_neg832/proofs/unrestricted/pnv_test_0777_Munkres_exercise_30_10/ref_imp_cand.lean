import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_30_10_assumed
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, Countable (X i)] (hX : ∀ i, ∃ D : Set (X i), Dense D) : ∃ D : Set (∀ i, X i), Dense D := by
  exact ⟨Set.univ, dense_univ⟩
