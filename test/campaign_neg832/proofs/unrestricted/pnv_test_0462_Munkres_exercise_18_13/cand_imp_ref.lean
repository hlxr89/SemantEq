import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hY : T2Space Y) {A : Set X} (hA : IsClosed (A : Set X)) {f : A → Y} (hf : Continuous f) : ∃! (g : X → Y), (∀ a : A, g a = f a) ∧ Continuous g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_13
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {A : Set X} {f : X → Y} (hf : ContinuousOn f A)
  (g : X → Y) (g_con : ContinuousOn g (closure A))
  (gExt : ∀ x : A, g x = f x) :
  ∀ (g' : X → Y), (ContinuousOn g' (closure A) ∧ (∀ x : A, g' x = f x)) → (∀ x : closure A, g x = g' x) := by
  have hFalse : False := by
    letI : TopologicalSpace Bool := ⊥
    let fEmpty : (∅ : Set Unit) → Bool := fun x ↦ x.2.elim
    have hfEmpty : Continuous fEmpty := continuous_of_discreteTopology
    obtain ⟨g₀, hg₀, huniq⟩ :=
      dummy_assumed (X := Unit) (Y := Bool) (A := ∅) (f := fEmpty)
        (inferInstance : T2Space Bool) isClosed_empty hfEmpty
    let gFalse : Unit → Bool := fun _ ↦ false
    let gTrue : Unit → Bool := fun _ ↦ true
    have hgFalse : (∀ a : (∅ : Set Unit), gFalse a = fEmpty a) ∧ Continuous gFalse := by
      constructor
      · intro a
        exact a.2.elim
      · exact continuous_const
    have hgTrue : (∀ a : (∅ : Set Unit), gTrue a = fEmpty a) ∧ Continuous gTrue := by
      constructor
      · intro a
        exact a.2.elim
      · exact continuous_const
    have hEq : gFalse = gTrue := (huniq gFalse hgFalse).trans (huniq gTrue hgTrue).symm
    have : false = true := congrFun hEq ()
    exact Bool.false_ne_true this
  exact hFalse.elim
