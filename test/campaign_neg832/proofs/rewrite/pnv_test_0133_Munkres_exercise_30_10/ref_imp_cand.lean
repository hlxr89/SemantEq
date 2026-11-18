import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_30_10_assumed
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {ι : Type*} [Fintype ι] {X : ι → Type*} [Nonempty ι] [∀ i, TopologicalSpace (X i)] (hX : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) : ∃ (s : Set (∀ i, X i)), Countable s ∧ Dense s := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  let n : ι → ℕ := fun i ↦ Classical.choose (he i)
  have hn : ∀ i, e (n i) = i := fun i ↦ Classical.choose_spec (he i)
  let p : (∀ k, X (e k)) → (∀ i, X i) := fun y i ↦ hn i ▸ y (n i)
  have hp : Continuous p := by
    rw [continuous_pi_iff]
    intro i
    change Continuous (fun y : (∀ k, X (e k)) ↦ hn i ▸ y (n i))
    have continuous_cast_apply : ∀ (j : ι) (k : ℕ) (hk : e k = j),
        Continuous (fun y : (∀ m, X (e m)) ↦ hk ▸ y k) := by
      intro j k hk
      cases hk
      exact continuous_apply k
    exact continuous_cast_apply i (n i) (hn i)
  have hp_surj : Function.Surjective p := by
    intro x
    refine ⟨fun k ↦ x (e k), ?_⟩
    funext i
    change (hn i ▸ x (e (n i))) = x i
    have cast_eval : ∀ (j : ι) (k : ℕ) (hk : e k = j),
        (hk ▸ x (e k)) = x j := by
      intro j k hk
      cases hk
      rfl
    exact cast_eval i (n i) (hn i)
  obtain ⟨s, hs, hd⟩ := exercise_30_10_assumed (X := fun k ↦ X (e k)) (fun k ↦ hX (e k))
  refine ⟨p '' s, Set.Countable.image hs p, ?_⟩
  exact hp_surj.denseRange.dense_image hp hd
