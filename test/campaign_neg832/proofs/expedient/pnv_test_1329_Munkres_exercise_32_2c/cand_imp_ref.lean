import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] [∀ i, Nonempty (π i)] (h : NormalSpace (∀ i, π i)) : ∀ i, NormalSpace (π i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  letI : NormalSpace (Π i, X i) := h2
  classical
  let x : ∀ i, X i := fun i ↦ Classical.choice (h i)
  intro i
  constructor
  intro s t hs ht hst
  have H := normal_separation
    (hs.preimage (continuous_apply i))
    (ht.preimage (continuous_apply i))
    (hst.preimage (fun y : (∀ i, X i) ↦ y i))
  have hcont : Continuous (Function.update x i : X i → (∀ i, X i)) :=
    continuous_const.update i continuous_id
  convert H.preimage hcont using 1 <;> ext a <;> simp
