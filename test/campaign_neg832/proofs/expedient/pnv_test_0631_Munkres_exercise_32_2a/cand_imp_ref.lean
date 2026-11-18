import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : β → Type*) [∀ s, TopologicalSpace (X s)] [∀ s, CompactSpace (X s)] [∀ s, T1Space (X s)] [∀ s, Nonempty (X s)] [CompactSpace (∀ s, X s)] [T1Space (∀ s, X s)] : ∀ (s : β), T1Space (X s) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2a
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  intro i
  letI : DecidableEq ι := Classical.decEq ι
  let x : ∀ j, X j := fun j => Classical.choice (h j)
  letI : T2Space (∀ j, X j) := h2
  have hi : Topology.IsEmbedding (Function.update x i) :=
    (show Function.LeftInverse (fun f : ∀ j, X j => f i) (Function.update x i) by
      intro y
      simp).isEmbedding (continuous_apply i) (continuous_const.update i continuous_id)
  exact hi.t2Space
