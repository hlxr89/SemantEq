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
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let Y := fun n : ℕ => (j : {i : ι // e i = n}) → X j.1
  letI (i : ι) : SeparableSpace (X i) :=
    ⟨h i⟩
  have hY : ∀ n, ∃ D : Set (Y n), D.Countable ∧ Dense D := by
    intro n
    exact exists_countable_dense (Y n)
  obtain ⟨D, hDc, hDd⟩ := exercise_30_10_assumed hY
  let E : (∀ n, Y n) ≃ₜ (∀ i, X i) :=
    { toEquiv :=
        { toFun := fun y i => y (e i) ⟨i, rfl⟩
          invFun := fun x _ j => x j.1
          left_inv := by
            intro y
            funext n j
            rcases j with ⟨i, hi⟩
            subst n
            rfl
          right_inv := by
            intro x
            rfl }
      continuous_toFun := continuous_pi fun i =>
        (continuous_apply (⟨i, rfl⟩ : {j : ι // e j = e i})).comp (continuous_apply (e i))
      continuous_invFun := continuous_pi fun n => continuous_pi fun j => continuous_apply j.1 }
  refine ⟨E '' D, Set.Countable.image hDc E, ?_⟩
  exact E.surjective.denseRange.dense_image E.continuous hDd
