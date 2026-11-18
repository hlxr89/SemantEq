import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u_1} {κ : Type u_2} [TopologicalSpace X] [T2Space X] (s : κ → Set X) (hs : ∀ (i : κ), Dense (s i)) (hX : SecondCountableTopology X) (hκ : Countable κ) : ∃ (t : Set X), Dense t ∧ t.Countable := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  letI (i : ℕ) : SeparableSpace (X i) := SeparableSpace.mk (h i)
  exact TopologicalSpace.exists_countable_dense (Π i, X i)
