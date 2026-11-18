import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_32_2c_assumed
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {I : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, NormalSpace (X i)] (hne : ∀ i, Nonempty (X i)) : NormalSpace (∀ i, X i) := by
  -- not proved: this is the false converse for arbitrary products of normal spaces
  sorry
