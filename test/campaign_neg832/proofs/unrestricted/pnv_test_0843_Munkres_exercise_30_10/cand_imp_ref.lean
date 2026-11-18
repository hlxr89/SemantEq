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
  exfalso
  obtain ⟨t, ht_count, ht_dense⟩ :=
    dummy_assumed (ι := Set (Set ℕ)) (X := fun _ => Bool)
      (fun _ => inferInstance) (fun _ => inferInstance)
  let F : Set (Set ℕ) → Set t := fun i => {x | x.1 i = true}
  have hF : Function.Injective F := by
    intro i j hij
    by_contra hne
    let p : Set (Set ℕ) → Bool := fun k => if k = i then true else false
    let U : Set (Set (Set ℕ) → Bool) := {x | x i = true ∧ x j = false}
    have hopen : IsOpen U := by
      have hi : Continuous (fun x : Set (Set ℕ) → Bool => x i) := continuous_apply i
      have hj : Continuous (fun x : Set (Set ℕ) → Bool => x j) := continuous_apply j
      have htrue : IsOpen ({true} : Set Bool) := isOpen_discrete _
      have hfalse : IsOpen ({false} : Set Bool) := isOpen_discrete _
      apply IsOpen.inter
      · simpa only [Set.mem_singleton_iff] using
          hi.isOpen_preimage ({true} : Set Bool) htrue
      · simpa only [Set.mem_singleton_iff] using
          hj.isOpen_preimage ({false} : Set Bool) hfalse
    have hp : p ∈ U := by
      constructor
      · simp [p]
      · simp [p, hne, Ne.symm hne]
    obtain ⟨x, hxt, hxU⟩ := ht_dense.exists_mem_open hopen ⟨p, hp⟩
    have hxi : (⟨x, hxt⟩ : t) ∈ F i := hxU.1
    have hxj : (⟨x, hxt⟩ : t) ∉ F j := by simp [F, hxU.2]
    exact hxj (hij ▸ hxi)
  letI : Countable t := ht_count
  obtain ⟨e, he⟩ := Countable.exists_injective_nat t
  let G : Set t → Set ℕ := fun A => e '' A
  have hG : Function.Injective G := (Set.image_injective).2 he
  exact Function.cantor_injective (G ∘ F) (hG.comp hF)
