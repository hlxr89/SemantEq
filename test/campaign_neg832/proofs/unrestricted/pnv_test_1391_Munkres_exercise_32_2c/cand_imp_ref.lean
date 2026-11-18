import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {I : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, NormalSpace (X i)] (hne : ∀ i, Nonempty (X i)) : NormalSpace (∀ i, X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  classical
  letI : NormalSpace (Π i, X i) := h2
  intro i
  let x₀ : ∀ j, X j := fun j => Classical.choice (h j)
  let e : X i → (∀ j, X j) := fun x => Function.update x₀ i x
  let p : (∀ j, X j) → X i := fun f => f i
  have he : Continuous e := continuous_const.update i continuous_id
  have hp : Continuous p := continuous_apply i
  refine { normal := ?_ }
  intro s t hs ht hst
  have hd : Disjoint (p ⁻¹' s) (p ⁻¹' t) := hst.preimage p
  have H : SeparatedNhds (p ⁻¹' s) (p ⁻¹' t) :=
    normal_separation (hs.preimage hp) (ht.preimage hp) hd
  apply (H.preimage he).mono
  · intro x hx
    change e x ∈ p ⁻¹' s
    simpa [e, p] using hx
  · intro x hx
    change e x ∈ p ⁻¹' t
    simpa [e, p] using hx
