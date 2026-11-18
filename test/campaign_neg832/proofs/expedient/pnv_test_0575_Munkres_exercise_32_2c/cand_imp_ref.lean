import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, NormalSpace (X i)] (hne : ∀ i, Nonempty (X i)) : NormalSpace (∀ i, X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  classical
  letI : NormalSpace (Π i, X i) := h2
  intro i
  let x₀ : Π i, X i := fun j ↦ Classical.choice (h j)
  let e : X i → (Π j, X j) := fun x ↦ Function.update x₀ i x
  have he : Continuous e := by
    exact continuous_const.update i continuous_id
  constructor
  intro s t hs ht hst
  have hp : Disjoint ((fun p : Π j, X j ↦ p i) ⁻¹' s)
      ((fun p : Π j, X j ↦ p i) ⁻¹' t) := by
    exact hst.preimage _
  have H := normal_separation (hs.preimage (continuous_apply i))
    (ht.preimage (continuous_apply i)) hp
  have hs' : e ⁻¹' ((fun p : Π j, X j ↦ p i) ⁻¹' s) = s := by
    ext x
    change (Function.update x₀ i x) i ∈ s ↔ x ∈ s
    rw [Function.update_self]
  have ht' : e ⁻¹' ((fun p : Π j, X j ↦ p i) ⁻¹' t) = t := by
    ext x
    change (Function.update x₀ i x) i ∈ t ↔ x ∈ t
    rw [Function.update_self]
  simpa only [hs', ht'] using H.preimage he
