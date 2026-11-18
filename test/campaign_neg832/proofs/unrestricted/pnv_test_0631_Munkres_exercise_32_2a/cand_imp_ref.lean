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
  classical
  letI : T2Space (Π i, X i) := h2
  intro i
  let x₀ : Π j, X j := fun j => Classical.choice (h j)
  let f : X i → (Π j, X j) := fun x => Function.update x₀ i x
  have hf : Continuous f := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [f] using (continuous_id : Continuous (fun x : X i => x))
    · simp only [f, Function.update_of_ne hji]
      exact continuous_const
  have hproj : Continuous (fun p : Π j, X j => p i) := continuous_apply i
  have hleft : Function.LeftInverse (fun p : Π j, X j => p i) f := by
    intro x
    simp [f]
  exact (hleft.isEmbedding hproj hf).t2Space
