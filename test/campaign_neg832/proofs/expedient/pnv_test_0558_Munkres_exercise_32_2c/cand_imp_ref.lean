import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] (hne : ∀ i, Nonempty (X i)) (h : NormalSpace (∀ i, X i)) : ∀ i, NormalSpace (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  classical
  let x₀ : ∀ i, X i := fun i => Classical.choice (h i)
  intro i
  let p : (∀ j, X j) → X i := fun x => x i
  let e : X i → (∀ j, X j) := fun x => Function.update x₀ i x
  have hp : Continuous p := continuous_apply i
  have he : Continuous e := continuous_pi fun j => by
    by_cases hji : j = i
    · subst j
      simpa only [e, Function.update_self] using
        (continuous_id : Continuous (fun x : X i => x))
    · simp only [e, Function.update_of_ne hji]
      exact continuous_const
  refine ⟨fun s t hs ht hd => ?_⟩
  have H : SeparatedNhds (p ⁻¹' s) (p ⁻¹' t) :=
    normal_separation (hs.preimage hp) (ht.preimage hp) (hd.preimage p)
  convert H.preimage he using 1 <;>
    ext x <;> simp only [Set.mem_preimage, p, e, Function.update_self]
