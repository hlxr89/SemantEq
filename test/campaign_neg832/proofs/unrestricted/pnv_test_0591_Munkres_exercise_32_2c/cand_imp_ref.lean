import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X α : Type} [tα : Nonempty α] {f : α → Type} [Π a, TopologicalSpace (f a)] [∀ a, NormalSpace (f a)] (h : NormalSpace (∀ a, f a)): ∀ a, NormalSpace (f a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  let x : ∀ i, X i := fun i ↦ Classical.choice (h i)
  intro i
  letI : NormalSpace (∀ i, X i) := h2
  letI : DecidableEq ι := Classical.decEq ι
  refine ⟨fun s t hs ht hst ↦ ?_⟩
  have hsep : SeparatedNhds
      ((fun y : ∀ i, X i ↦ y i) ⁻¹' s)
      ((fun y : ∀ i, X i ↦ y i) ⁻¹' t) :=
    normal_separation (hs.preimage (continuous_apply i))
      (ht.preimage (continuous_apply i))
      (hst.preimage (fun y : ∀ i, X i ↦ y i))
  have hcont : Continuous (fun a : X i ↦ Function.update x i a) :=
    continuous_const.update i continuous_id
  have hs_eq :
      (fun a : X i ↦ Function.update x i a) ⁻¹'
        ((fun y : ∀ i, X i ↦ y i) ⁻¹' s) = s := by
    ext a
    simp
  have ht_eq :
      (fun a : X i ↦ Function.update x i a) ⁻¹'
        ((fun y : ∀ i, X i ↦ y i) ⁻¹' t) = t := by
    ext a
    simp
  have hresult : SeparatedNhds
      ((fun a : X i ↦ Function.update x i a) ⁻¹'
        ((fun y : ∀ i, X i ↦ y i) ⁻¹' s))
      ((fun a : X i ↦ Function.update x i a) ⁻¹'
        ((fun y : ∀ i, X i ↦ y i) ⁻¹' t)) :=
    hsep.preimage hcont
  rw [hs_eq, ht_eq] at hresult
  exact hresult
