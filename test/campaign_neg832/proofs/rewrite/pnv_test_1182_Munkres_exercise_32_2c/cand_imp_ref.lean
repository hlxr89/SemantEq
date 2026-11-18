import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} {X : α → Type*} [∀ a, TopologicalSpace (X a)] [h : NormalSpace (Π a, X a)] (a : α) [Nonempty (X a)] : NormalSpace (X a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  letI : NormalSpace (Π i, X i) := h2
  intro i
  letI : Nonempty (X i) := h i
  exact dummy_assumed i
