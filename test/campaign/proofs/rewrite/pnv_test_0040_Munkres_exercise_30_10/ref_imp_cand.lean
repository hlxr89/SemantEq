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
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  choose D hD_countable hD_dense using h
  let Y : ℕ → Type _ := fun n => ∀ j : {i : ι // e i = n}, X j.1
  have hY : ∀ n, ∃ s : Set (Y n), s.Countable ∧ Dense s := by
    intro n
    letI : Subsingleton {i : ι // e i = n} :=
      ⟨fun a b => Subtype.ext (he (a.2.trans b.2.symm))⟩
    letI : Finite {i : ι // e i = n} :=
      Finite.of_injective (fun _ => PUnit.unit) (fun _ _ _ => Subsingleton.elim _ _)
    refine ⟨Set.pi Set.univ (fun j => D j.1), Set.countable_univ_pi (fun j => hD_countable j.1), ?_⟩
    exact dense_pi Set.univ (fun j _ => hD_dense j.1)
  obtain ⟨S, hS_countable, hS_dense⟩ := exercise_30_10_assumed hY
  let curryHomeomorph :
      ((z : (n : ℕ) × {i : ι // e i = n}) → X z.2.1) ≃ₜ
        (∀ n, ∀ j : {i : ι // e i = n}, X j.1) :=
    { toEquiv :=
        { toFun := fun f n j => f ⟨n, j⟩
          invFun := fun f z => f z.1 z.2
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := continuous_pi fun (n : ℕ) =>
        continuous_pi fun (j : {i : ι // e i = n}) =>
          continuous_apply (⟨n, j⟩ : (n : ℕ) × {i : ι // e i = n})
      continuous_invFun := continuous_pi fun z => by
        change Continuous (fun f : (∀ n, ∀ j : {i : ι // e i = n}, X j.1) => f z.1 z.2)
        exact (continuous_apply z.2).comp (continuous_apply z.1) }
  let indexEquiv : ((n : ℕ) × {i : ι // e i = n}) ≃ ι := Equiv.sigmaFiberEquiv e
  let E : (∀ n, Y n) ≃ₜ (∀ i, X i) :=
    curryHomeomorph.symm.trans (Homeomorph.piCongrLeft indexEquiv)
  refine ⟨E '' S, Set.Countable.image hS_countable E, ?_⟩
  exact E.surjective.denseRange.dense_image E.continuous hS_dense
