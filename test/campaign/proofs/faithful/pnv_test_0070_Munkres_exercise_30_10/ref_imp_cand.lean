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
theorem dummy {X : Type*} [TopologicalSpace X] {ι : Type*} [Countable ι] {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (h : ∀ i, ∃ S : Set (π i), S.Countable ∧ Dense S) : ∃ S : Set (∀ i, π i), S.Countable ∧ Dense S := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI : IsEmpty ι := hι
      obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed
        (X := fun _ => Unit)
        (fun _ => ⟨Set.univ, Set.countable_univ, dense_univ⟩)
      let f : (ℕ → Unit) → (∀ i, π i) := fun _ i => isEmptyElim i
      have hf : Continuous f := by
        apply continuous_pi
        intro i
        exact isEmptyElim i
      have hfs : Function.Surjective f := by
        intro y
        refine ⟨fun _ => PUnit.unit, ?_⟩
        funext i
        exact isEmptyElim i
      exact ⟨f '' S, Set.Countable.image hSc.to_set f,
        hfs.denseRange.dense_image hf hSd⟩
  | inr hι =>
      letI : Nonempty ι := hι
      obtain ⟨g, hg⟩ := exists_surjective_nat ι
      let r : ι → ℕ := Function.surjInv hg
      have hr : Function.RightInverse r g := Function.rightInverse_surjInv hg
      obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed (X := fun n => π (g n))
        (fun n => h (g n))
      have cast_continuous {a b : ι} (hab : a = b) :
          Continuous (fun z : π a => cast (congrArg π hab) z) := by
        subst b
        simpa using (continuous_id : Continuous (id : π a → π a))
      let f : (∀ n, π (g n)) → (∀ i, π i) := fun x i =>
        cast (congrArg π (hr i)) (x (r i))
      have hf : Continuous f := by
        apply continuous_pi
        intro i
        exact (cast_continuous (hr i)).comp
          (continuous_apply (r i) : Continuous (fun x : ∀ n, π (g n) => x (r i)))
      have hfs : Function.Surjective f := by
        intro y
        refine ⟨fun n => y (g n), ?_⟩
        funext i
        change cast (congrArg π (hr i)) (y (g (r i))) = y i
        apply eq_of_heq
        exact (cast_heq _ _).trans (congr_arg_heq y (hr i))
      exact ⟨f '' S, Set.Countable.image hSc.to_set f,
        hfs.denseRange.dense_image hf hSd⟩
