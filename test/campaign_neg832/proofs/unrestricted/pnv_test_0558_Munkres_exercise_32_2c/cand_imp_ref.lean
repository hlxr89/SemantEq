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
  let x₀ : ∀ j, X j := fun j => Classical.choice (h j)
  intro i
  letI : NormalSpace (∀ j, X j) := h2
  let sec : X i → (∀ j, X j) := fun x => Function.update x₀ i x
  have hsec : Continuous sec := by
    simpa only [sec] using
      ((continuous_const : Continuous (fun _ : X i => x₀)).update i continuous_id)
  constructor
  intro s t hs ht hst
  have hs' : IsClosed ((fun x : ∀ j, X j => x i) ⁻¹' s) :=
    hs.preimage (continuous_apply i)
  have ht' : IsClosed ((fun x : ∀ j, X j => x i) ⁻¹' t) :=
    ht.preimage (continuous_apply i)
  have hst' : Disjoint ((fun x : ∀ j, X j => x i) ⁻¹' s)
      ((fun x : ∀ j, X j => x i) ⁻¹' t) :=
    hst.preimage (fun x : ∀ j, X j => x i)
  rcases normal_separation hs' ht' hst' with
    ⟨u, v, hu, hv, hsu, htv, huv⟩
  refine ⟨sec ⁻¹' u, sec ⁻¹' v, hu.preimage hsec,
    hv.preimage hsec, ?_, ?_, huv.preimage sec⟩
  · intro x hx
    apply hsu
    simpa [sec] using hx
  · intro x hx
    apply htv
    simpa [sec] using hx
