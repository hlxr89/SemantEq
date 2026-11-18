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
  letI : NormalSpace (Π i, X i) := h2
  intro i
  let x : Π j, X j := fun j => Classical.choice (h j)
  let e : X i → (Π j, X j) := fun y => Function.update x i y
  have he : Continuous e := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [e] using (continuous_id : Continuous (id : X i → X i))
    · simpa [e, hji] using (continuous_const : Continuous (fun _ : X i => x j))
  refine ⟨?_⟩
  intro s t hs ht hst
  let p : (Π j, X j) → X i := fun z => z i
  have hp : Continuous p := continuous_apply i
  have H : SeparatedNhds (p ⁻¹' s) (p ⁻¹' t) :=
    NormalSpace.normal (p ⁻¹' s) (p ⁻¹' t) (hs.preimage hp) (ht.preimage hp) (hst.preimage p)
  have hpe : p ∘ e = id := by
    funext y
    exact Function.update_self i y x
  have H' := H.preimage he
  change SeparatedNhds ((p ∘ e) ⁻¹' s) ((p ∘ e) ⁻¹' t) at H'
  simpa [hpe] using H'
