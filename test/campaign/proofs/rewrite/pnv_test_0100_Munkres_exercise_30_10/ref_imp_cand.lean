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
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI : IsEmpty ι := hempty
      have hY : ∀ n : ℕ, ∃ D : Set PUnit.{1}, Countable D ∧ Dense D := fun _ =>
        ⟨Set.univ, Set.countable_univ, dense_univ⟩
      obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed hY
      let r : (ℕ → PUnit.{1}) → (∀ i, X i) := fun _ i => isEmptyElim i
      have hr_cont : Continuous r := by
        apply continuous_pi
        intro i
        exact isEmptyElim i
      have hr_surj : Function.Surjective r := by
        intro x
        refine ⟨fun _ => PUnit.unit, ?_⟩
        funext i
        exact isEmptyElim i
      refine ⟨r '' S, Set.Countable.image hSc r, ?_⟩
      have hd : DenseRange (r ∘ ((↑) : S → (ℕ → PUnit.{1}))) :=
        hr_surj.denseRange.comp (denseRange_subtype_val.mpr hSd) hr_cont
      rw [show r '' S = Set.range (r ∘ ((↑) : S → (ℕ → PUnit.{1}))) by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨y, y.property, rfl⟩]
      exact hd
  | inr hnonempty =>
    letI : Nonempty ι := hnonempty
    obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
    let idx : ℕ → ι := fun n => if hn : ∃ i, e i = n then Classical.choose hn else Classical.choice inferInstance
    let Y := fun n => X (idx n)
    letI (n : ℕ) : TopologicalSpace (Y n) := inferInstance
    have hidx (i : ι) : idx (e i) = i := by
      dsimp only [idx]
      rw [dif_pos (show ∃ j, e j = e i from ⟨i, rfl⟩)]
      apply he
      exact Classical.choose_spec (show ∃ j, e j = e i from ⟨i, rfl⟩)
    have hY : ∀ n, ∃ D : Set (Y n), Countable D ∧ Dense D := by
      intro n
      exact h (idx n)
    obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed hY
    let r : (∀ n, Y n) → (∀ i, X i) := fun y i =>
      cast (congrArg X (hidx i)) (y (e i))
    have cast_continuous (n : ℕ) (i : ι) (hi : idx n = i) :
        Continuous (fun y : (∀ n, Y n) => cast (congrArg X hi) (y n)) := by
      cases hi
      exact continuous_apply n
    have cast_section (n : ℕ) (i : ι) (hi : idx n = i) (x : ∀ i, X i) :
        cast (congrArg X hi) (x (idx n)) = x i := by
      cases hi
      rfl
    have hr_cont : Continuous r := by
      apply continuous_pi
      intro i
      exact cast_continuous (e i) i (hidx i)
    have hr_surj : Function.Surjective r := by
      intro x
      let q : ∀ n, Y n := fun n => x (idx n)
      refine ⟨q, ?_⟩
      funext i
      dsimp only [r, q]
      exact cast_section (e i) i (hidx i) x
    refine ⟨r '' S, Set.Countable.image hSc r, ?_⟩
    have hd : DenseRange (r ∘ ((↑) : S → (∀ n, Y n))) :=
      hr_surj.denseRange.comp (denseRange_subtype_val.mpr hSd) hr_cont
    rw [show r '' S = Set.range (r ∘ ((↑) : S → (∀ n, Y n))) by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.property, rfl⟩]
    exact hd
