import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] {ι : Type*} [Countable ι] {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (h : ∀ i, ∃ S : Set (π i), S.Countable ∧ Dense S) : ∃ S : Set (∀ i, π i), S.Countable ∧ Dense S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  exact dummy_assumed (X := Unit) (ι := ℕ) (π := X) h
