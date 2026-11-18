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
  intro i
  let x : ∀ j, X j := fun j => Classical.choice (h j)
  let e : X i → (∀ j, X j) := fun y => Function.update x i y
  have he : Continuous e := continuous_const.update i continuous_id
  letI := h2
  constructor
  intro s t hs ht hst
  have hs' : IsClosed ((fun f : ∀ j, X j => f i) ⁻¹' s) :=
    hs.preimage (continuous_apply i)
  have ht' : IsClosed ((fun f : ∀ j, X j => f i) ⁻¹' t) :=
    ht.preimage (continuous_apply i)
  have hst' : Disjoint ((fun f : ∀ j, X j => f i) ⁻¹' s)
      ((fun f : ∀ j, X j => f i) ⁻¹' t) := hst.preimage _
  have hei : (fun y : X i => (e y) i) = id := by
    funext y
    simp [e]
  have H := (normal_separation hs' ht' hst').preimage he
  change SeparatedNhds ((fun y => (e y) i) ⁻¹' s) ((fun y => (e y) i) ⁻¹' t) at H
  rw [hei] at H
  simpa using H
