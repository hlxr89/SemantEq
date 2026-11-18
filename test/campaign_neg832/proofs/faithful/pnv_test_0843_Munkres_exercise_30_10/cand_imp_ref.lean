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
  choose d hd_count hd_dense using h
  let D : ℕ → Type _ := fun i => d i
  let f : (∀ i, D i) → (∀ i, X i) := fun x i => x i
  letI (i : ℕ) : Countable (D i) := Set.Countable.to_subtype (hd_count i)
  obtain ⟨t, ht_count, ht_dense⟩ :=
    dummy_assumed (X := D) (fun _ => inferInstance) (fun _ => inferInstance)
  refine ⟨f '' t, Set.Countable.image ht_count f, ?_⟩
  apply (DenseRange.piMap (fun i => denseRange_subtype_val.mpr (hd_dense i))).dense_image
  · exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  · exact ht_dense
