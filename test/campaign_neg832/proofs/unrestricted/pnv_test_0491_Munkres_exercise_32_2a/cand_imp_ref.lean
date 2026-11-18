import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type u} {X : ι → Type v} (h : ∀ α, Nonempty (X α)) [∀ α, TopologicalSpace (X α)] [∀ α, T2Space (X α)] : T2Space (∀ α, X α) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2a
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  intro i
  letI : T2Space (Π i, X i) := h2
  classical
  let x₀ : ∀ j, X j := fun j => Classical.choice (h j)
  let f : X i → (∀ j, X j) := fun x => Function.update x₀ i x
  have hf : Continuous f := by
    exact (continuous_update i).comp (continuous_const.prodMk continuous_id)
  have heval : Continuous (fun p : (∀ j, X j) => p i) := continuous_apply i
  have hleft : Function.LeftInverse (fun p : (∀ j, X j) => p i) f := by
    intro x
    simp [f]
  exact (hleft.isEmbedding heval hf).t2Space
