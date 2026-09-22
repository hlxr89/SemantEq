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
theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ D : Set (X i), Countable D ∧ Dense D) : ∃ D : Set (Π i, X i), Countable D ∧ Dense D := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let G : (Π _ : ℕ, PUnit.{1}) → (Π i, X i) := fun _ i => isEmptyElim i
      obtain ⟨D, hD_countable, hD_dense⟩ :=
        exercise_30_10_assumed (X := fun _ => PUnit.{1})
          (fun _ => ⟨Set.univ, Set.countable_univ, dense_univ⟩)
      refine ⟨G '' D, Set.Countable.image hD_countable G, ?_⟩
      have hG_surj : Function.Surjective G := by
        intro y
        refine ⟨fun _ => PUnit.unit, ?_⟩
        funext i
        exact isEmptyElim i
      have hG_cont : Continuous G := by
        simpa [G] using
          (continuous_const : Continuous (fun _ : (Π _ : ℕ, PUnit.{1}) =>
            (fun i : ι => isEmptyElim i : Π i, X i)))
      exact hG_surj.denseRange.dense_image hG_cont hD_dense
  | inr hι =>
      letI : Nonempty ι := hι
      obtain ⟨p, hp⟩ := exists_surjective_nat ι
      choose q hq using hp
      let G : (Π n, X (p n)) → (Π i, X i) :=
        fun x i => cast (congrArg X (hq i)) (x (q i))
      obtain ⟨D, hD_countable, hD_dense⟩ :=
        exercise_30_10_assumed (X := fun n => X (p n)) (fun n => h (p n))
      refine ⟨G '' D, Set.Countable.image hD_countable G, ?_⟩
      have continuous_cast_apply (n : ℕ) (i : ι) (e : p n = i) :
          Continuous (fun x : (Π n, X (p n)) =>
            cast (congrArg X e) (x n)) := by
        subst i
        simpa using
          (continuous_apply n : Continuous (fun x : (Π n, X (p n)) => x n))
      have hG_cont : Continuous G := by
        apply continuous_pi
        intro i
        exact continuous_cast_apply (q i) i (hq i)
      have cast_apply (n : ℕ) (i : ι) (e : p n = i) (y : Π i, X i) :
          cast (congrArg X e) (y (p n)) = y i := by
        subst i
        rfl
      have hG_surj : Function.Surjective G := by
        intro y
        refine ⟨fun n => y (p n), ?_⟩
        funext i
        exact cast_apply (q i) i (hq i) y
      exact hG_surj.denseRange.dense_image hG_cont hD_dense
