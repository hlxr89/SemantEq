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
  have h := dummy_assumed (X := Unit) (Y := Bool) (hY := inferInstance)
    (A := (∅ : Set Unit)) (f := fun a => False.elim a.property)
    isClosed_empty (by continuity)
  rcases h with ⟨_, _, h_unique⟩
  have h_false := h_unique (fun _ : Unit => false) ⟨by
    intro a
    exact False.elim a.property
  , continuous_const⟩
  have h_true := h_unique (fun _ : Unit => true) ⟨by
    intro a
    exact False.elim a.property
  , continuous_const⟩
  have : false = true := congrFun (h_false.trans h_true.symm) ()
  contradiction
