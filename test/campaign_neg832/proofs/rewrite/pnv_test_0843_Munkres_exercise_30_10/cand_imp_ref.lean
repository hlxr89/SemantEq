import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (hX : ∀ i, SeparableSpace (X i)) (s : ∀ i, Countable (X i)) : ∃ t : Set (∀ i, X i), Countable t ∧ Dense t := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  classical
  choose S hS_countable hS_dense using h
  letI (i : ℕ) : Countable (S i) := Set.Countable.to_subtype (hS_countable i)
  obtain ⟨t, ht_countable, ht_dense⟩ :=
    dummy_assumed (X := fun i => S i) (fun _ => inferInstance) (fun _ => inferInstance)
  let f : (∀ i, S i) → (∀ i, X i) := Pi.map (fun _ => Subtype.val)
  have hf_dense : DenseRange f := by
    exact DenseRange.piMap (fun i => denseRange_subtype_val.mpr (hS_dense i))
  have hf_continuous : Continuous f := by
    exact Continuous.piMap (fun _ => continuous_subtype_val)
  exact ⟨f '' t, Set.Countable.image ht_countable f,
    hf_dense.dense_image hf_continuous ht_dense⟩
