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
  let x : ∀ i, X i := fun i ↦ Classical.choice (h i)
  letI : NormalSpace (∀ i, X i) := h2
  intro i
  constructor
  intro s t hs ht hd
  have H := NormalSpace.normal
    ((fun y : ∀ i, X i ↦ y i) ⁻¹' s) ((fun y : ∀ i, X i ↦ y i) ⁻¹' t)
    (hs.preimage (continuous_apply i)) (ht.preimage (continuous_apply i))
    (hd.preimage (fun y : ∀ i, X i ↦ y i))
  have hc : Continuous (fun a : X i ↦ Function.update x i a) :=
    continuous_const.update i continuous_id
  refine (H.preimage hc).mono ?_ ?_
  · intro a ha
    simpa only [Set.mem_preimage, Function.update_self] using ha
  · intro a ha
    simpa only [Set.mem_preimage, Function.update_self] using ha
