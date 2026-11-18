import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} {X : ι → Type*} [tX : ∀ i, TopologicalSpace (X i)] (h : ∀ i j, NormalSpace (X i ⊕ X j)) (h' : ∀ i, Nonempty (X i)) : NormalSpace (∀ i, X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  classical
  let x : ∀ i, X i := fun i => (h i).some
  intro i
  let e : X i → (∀ j, X j) := Function.update x i
  have he : Continuous e := continuous_const.update i continuous_id
  letI : NormalSpace (∀ j, X j) := h2
  constructor
  intro s t hs ht hst
  have hsep : SeparatedNhds
      ((fun y : ∀ j, X j => y i) ⁻¹' s)
      ((fun y : ∀ j, X j => y i) ⁻¹' t) :=
    normal_separation (hs.preimage (continuous_apply i))
      (ht.preimage (continuous_apply i)) (hst.preimage _)
  convert hsep.preimage he using 1 <;> ext z <;> simp [e]
