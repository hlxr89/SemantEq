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
theorem dummy {X : Type*} [TopologicalSpace X] {ι : Type*} [Countable ι] {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (h : ∀ i, ∃ S : Set (π i), S.Countable ∧ Dense S) : ∃ S : Set (∀ i, π i), S.Countable ∧ Dense S := by
  letI (i : ι) : SeparableSpace (π i) := ⟨h i⟩
  exact TopologicalSpace.exists_countable_dense _
