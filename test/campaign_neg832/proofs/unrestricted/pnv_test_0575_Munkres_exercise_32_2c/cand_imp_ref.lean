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
  letI : NormalSpace (∀ i, X i) := h2
  intro i
  let x₀ : ∀ j, X j := fun j => Classical.choice (h j)
  let f : X i → (∀ j, X j) := fun x j =>
    if hij : j = i then hij ▸ x else x₀ j
  have hf : Continuous f := by
    apply continuous_pi
    intro j
    by_cases hij : j = i
    · subst j
      simpa [f] using (continuous_id : Continuous (id : X i → X i))
    · simpa [f, hij] using (continuous_const : Continuous (fun _ : X i => x₀ j))
  refine ⟨?_⟩
  intro s t hs ht hst
  have hs' : IsClosed ((Function.eval i) ⁻¹' s) := hs.preimage (continuous_apply i)
  have ht' : IsClosed ((Function.eval i) ⁻¹' t) := ht.preimage (continuous_apply i)
  have hst' : Disjoint ((Function.eval i) ⁻¹' s) ((Function.eval i) ⁻¹' t) :=
    hst.preimage (Function.eval i)
  have H := normal_separation hs' ht' hst'
  have hfs : f ⁻¹' ((Function.eval i) ⁻¹' s) = s := by
    ext x
    change f x i ∈ s ↔ x ∈ s
    simp [f]
  have hft : f ⁻¹' ((Function.eval i) ⁻¹' t) = t := by
    ext x
    change f x i ∈ t ↔ x ∈ t
    simp [f]
  simpa [hfs, hft] using H.preimage hf
