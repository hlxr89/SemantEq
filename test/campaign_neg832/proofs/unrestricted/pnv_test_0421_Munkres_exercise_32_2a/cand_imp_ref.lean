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
  let x₀ : ∀ i, X i := fun i ↦ Classical.choice (h i)
  intro i
  let s : X i → (∀ j, X j) := fun x ↦ Function.update x₀ i x
  have hs : Continuous s := by
    dsimp [s]
    fun_prop
  have hleft : Function.LeftInverse (fun p : ∀ j, X j ↦ p i) s := by
    intro x
    simp [s]
  have he : Topology.IsEmbedding s :=
    Topology.IsEmbedding.of_leftInverse hleft (continuous_apply i) hs
  letI : T2Space (∀ j, X j) := h2
  exact he.t2Space
