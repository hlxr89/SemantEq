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
      have hU : ∀ n : ℕ, ∃ s : Set Unit, Countable s ∧ Dense s := fun _ =>
        ⟨Set.univ, Set.countable_coe_iff.mpr Set.countable_univ, dense_univ⟩
      obtain ⟨S, hSc, hSd⟩ :=
        exercise_30_10_assumed (X := fun _ => Unit) hU
      let q : (∀ _ : ℕ, Unit) → (∀ i, π i) := fun _ i => isEmptyElim i
      have hq : Continuous q := by
        apply continuous_pi
        intro i
        exact isEmptyElim i
      have hqs : Function.Surjective q := by
        intro y
        exact ⟨fun _ => (), Subsingleton.elim _ _⟩
      refine ⟨q '' S, (Set.countable_coe_iff.mp hSc).image q, ?_⟩
      exact hqs.denseRange.dense_image hq hSd
  | inr hι =>
      letI : Nonempty ι := hι
      obtain ⟨f, hf⟩ := exists_surjective_nat ι
      let g : ι → ℕ := fun i => Classical.choose (hf i)
      have hg : ∀ i, f (g i) = i := fun i => Classical.choose_spec (hf i)
      let Y := fun n : ℕ => π (f n)
      letI : ∀ n, TopologicalSpace (Y n) := fun n => inferInstanceAs (TopologicalSpace (π (f n)))
      have hY : ∀ n, ∃ s : Set (Y n), Countable s ∧ Dense s := by
        intro n
        exact h (f n)
      obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed hY
      let q : (∀ n, Y n) → (∀ i, π i) := fun x i =>
        (congrArg π (hg i)).mp (x (g i))
      have hq : Continuous q := by
        apply continuous_pi
        intro i
        have hc (n : ℕ) (j : ι) (e : f n = j) :
            Continuous (fun x : (∀ n, Y n) => (congrArg π e).mp (x n)) := by
          cases e
          exact continuous_apply n
        exact hc (g i) i (hg i)
      have hqs : Function.Surjective q := by
        intro y
        let x : ∀ n, Y n := fun n => y (f n)
        refine ⟨x, funext fun i => ?_⟩
        simp only [q, x]
        have hc (j k : ι) (e : j = k) :
            (congrArg π e).mp (y j) = y k := by
          cases e
          rfl
        exact hc (f (g i)) i (hg i)
      refine ⟨q '' S, (Set.countable_coe_iff.mp hSc).image q, ?_⟩
      exact hqs.denseRange.dense_image hq hSd
