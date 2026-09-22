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
theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ D : Set (X i), D.Countable ∧ Dense D) : ∃ D : Set (Π i, X i), D.Countable ∧ Dense D := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let Y : ℕ → Type := fun _ => PUnit
      have hY : ∀ n, ∃ D : Set (Y n), D.Countable ∧ Dense D := by
        intro n
        exact ⟨Set.univ, Set.countable_univ, dense_univ⟩
      obtain ⟨D, hDc, hDd⟩ := exercise_30_10_assumed hY
      let F : (∀ n, Y n) → (∀ i, X i) := fun _ i => isEmptyElim i
      have hFc : Continuous F := continuous_pi fun i => isEmptyElim i
      have hFs : Function.Surjective F := by
        intro x
        exact ⟨fun _ => PUnit.unit, Subsingleton.elim _ _⟩
      exact ⟨F '' D, Set.Countable.image hDc F,
        hFs.denseRange.dense_image hFc hDd⟩
  | inr hι =>
      let f : ι → ℕ := Classical.choose (Countable.exists_injective_nat ι)
      have hf : Function.Injective f := Classical.choose_spec (Countable.exists_injective_nat ι)
      let g : ℕ → ι := Function.invFun f
      have hgf : Function.LeftInverse g f := Function.leftInverse_invFun hf
      let Y := fun n : ℕ => X (g n)
      have hY : ∀ n, ∃ D : Set (Y n), D.Countable ∧ Dense D := fun n => h (g n)
      obtain ⟨D, hDc, hDd⟩ := exercise_30_10_assumed hY
      let F : (∀ n, Y n) → (∀ i, X i) := fun p i => hgf i ▸ p (f i)
      have continuous_cast_apply (n : ℕ) (i : ι) (q : g n = i) :
          Continuous (fun p : ∀ n, Y n => q ▸ (show X (g n) from p n)) := by
        subst i
        exact continuous_apply n
      have hFc : Continuous F := continuous_pi fun i => by
        exact continuous_cast_apply (f i) i (hgf i)
      have hFs : Function.Surjective F := by
        intro x
        refine ⟨fun n => x (g n), ?_⟩
        funext i
        change hgf i ▸ x (g (f i)) = x i
        have cast_apply (j k : ι) (q : j = k) : q ▸ x j = x k := by
          subst k
          rfl
        exact cast_apply (g (f i)) i (hgf i)
      exact ⟨F '' D, Set.Countable.image hDc F,
        hFs.denseRange.dense_image hFc hDd⟩
