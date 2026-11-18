import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type u} {X : α → Type v} [∀ a : α, TopologicalSpace (X a)] [∀ (a : α), T2Space (X a)] : T2Space (∀ a, X a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2a
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  classical
  letI : T2Space (Π i, X i) := h2
  let b : Π i, X i := fun i => Classical.choice (h i)
  intro i
  let s : X i → Π i, X i := fun x => Function.update b i x
  have hs : Topology.IsEmbedding s :=
    (show Function.LeftInverse (fun p : Π i, X i => p i) s by
      intro x
      simp [s]).isEmbedding (continuous_apply i)
        (continuous_const.update i continuous_id)
  exact hs.t2Space
