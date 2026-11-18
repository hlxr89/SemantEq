import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] (h : T2Space (∀ i, X i)) (i : ι) : T2Space (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2a
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  classical
  intro i
  let x : ∀ i, X i := fun i => Classical.choice (h i)
  letI : T2Space (∀ i, X i) := h2
  exact T2Space.of_injective_continuous (Function.update_injective x i)
    (continuous_const.update i continuous_id)
