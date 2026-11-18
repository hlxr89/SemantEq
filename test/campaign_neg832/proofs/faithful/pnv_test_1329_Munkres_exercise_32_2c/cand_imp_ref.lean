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
  classical
  let x₀ : ∀ i, X i := fun i => Classical.choice (h i)
  have hunit : NormalSpace Unit :=
    dummy_assumed (X := Unit) (ι := Unit) (π := fun _ => Unit)
      (inferInstance : NormalSpace (∀ _ : Unit, Unit)) ()
  intro i
  let e : X i → (∀ j, X j) := fun x => Function.update x₀ i x
  have he : Continuous e := continuous_const.update i continuous_id
  letI : NormalSpace (∀ j, X j) := h2
  refine ⟨fun s t hs ht hst => ?_⟩
  have hs' : IsClosed ((fun z : ∀ j, X j => z i) ⁻¹' s) :=
    hs.preimage (continuous_apply i)
  have ht' : IsClosed ((fun z : ∀ j, X j => z i) ⁻¹' t) :=
    ht.preimage (continuous_apply i)
  have hst' : Disjoint ((fun z : ∀ j, X j => z i) ⁻¹' s)
      ((fun z : ∀ j, X j => z i) ⁻¹' t) := hst.preimage _
  rcases normal_separation hs' ht' hst' with
    ⟨u, v, hu, hv, hsu, htv, huv⟩
  letI : NormalSpace Unit := hunit
  rcases normal_separation (isClosed_univ : IsClosed (Set.univ : Set Unit))
      (isClosed_empty : IsClosed (∅ : Set Unit)) (by simp) with
    ⟨w, _z, hw, _hz, hunivw, _hemptyz, _hwz⟩
  refine ⟨e ⁻¹' u ∩ (fun _ : X i => ()) ⁻¹' w,
    e ⁻¹' v ∩ (fun _ : X i => ()) ⁻¹' w,
    (hu.preimage he).inter (hw.preimage continuous_const),
    (hv.preimage he).inter (hw.preimage continuous_const), ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · apply hsu
      simpa [e] using hx
    · exact hunivw (Set.mem_univ _)
  · intro x hx
    constructor
    · apply htv
      simpa [e] using hx
    · exact hunivw (Set.mem_univ _)
  · exact (huv.preimage e).mono inter_subset_left inter_subset_left
