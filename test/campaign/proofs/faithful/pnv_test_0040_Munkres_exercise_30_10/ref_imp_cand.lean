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
theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ D : Set (X i), D.Countable ∧ Dense D) : ∃ D : Set (∀ i, X i), D.Countable ∧ Dense D := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI : IsEmpty ι := hι
      obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed (X := fun _ => Unit) (fun _ =>
        ⟨Set.univ, Set.countable_univ, dense_univ⟩)
      let r : (∀ _ : ℕ, Unit) → (∀ i, X i) := fun _ i => isEmptyElim i
      refine ⟨r '' S, Countable.image hSc r, ?_⟩
      have hr_surj : Function.Surjective r := fun _ => ⟨fun _ => (),
        Subsingleton.elim _ _⟩
      exact hr_surj.denseRange.dense_image (continuous_pi fun i => isEmptyElim i) hSd
  | inr hι =>
      letI : Nonempty ι := hι
      obtain ⟨f, hf⟩ := exists_surjective_nat ι
      choose g hg using hf
      obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed (X := fun n => X (f n)) (fun n => h (f n))
      let r : (∀ n, X (f n)) → (∀ i, X i) := fun x i => hg i ▸ x (g i)
      have continuous_cast_apply {n : ℕ} {i : ι} (e : f n = i) :
          Continuous (fun x : (∀ n, X (f n)) => e ▸ x n) := by
        cases e
        exact continuous_apply n
      have hr_cont : Continuous r := by
        apply continuous_pi
        intro i
        exact continuous_cast_apply (hg i)
      have cast_apply {a b : ι} (e : a = b) (y : ∀ i, X i) : e ▸ y a = y b := by
        cases e
        rfl
      have hr_surj : Function.Surjective r := by
        intro y
        refine ⟨fun n => y (f n), ?_⟩
        funext i
        exact cast_apply (hg i) y
      refine ⟨r '' S, Countable.image hSc r, ?_⟩
      exact hr_surj.denseRange.dense_image hr_cont hSd
