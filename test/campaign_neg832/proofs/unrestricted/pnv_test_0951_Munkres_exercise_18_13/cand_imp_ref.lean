import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} {f : X → Y} (hA : IsClosed A) (hf : ContinuousOn f A) (hf' : ∀ x : X, x ∈ A → ContinuousWithinAt f A x) : ∃! g : X → Y, Continuous g ∧ EqOn f g A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_13
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {A : Set X} {f : X → Y} (hf : ContinuousOn f A)
  (g : X → Y) (g_con : ContinuousOn g (closure A))
  (gExt : ∀ x : A, g x = f x) :
  ∀ (g' : X → Y), (ContinuousOn g' (closure A) ∧ (∀ x : A, g' x = f x)) → (∀ x : closure A, g x = g' x) := by
  have h := dummy_assumed
    (X := Unit) (Y := Bool) (A := (∅ : Set Unit))
    (f := fun _ => false) isClosed_empty (continuousOn_empty _)
    (by
      intro x hx
      simp at hx)
  obtain ⟨extension, hextension, hunique⟩ := h
  have hfalse :
      Continuous (fun _ : Unit => false) ∧
        EqOn (fun _ : Unit => false) (fun _ : Unit => false) ∅ := by
    exact ⟨continuous_const, Set.eqOn_refl _ _⟩
  have htrue :
      Continuous (fun _ : Unit => true) ∧
        EqOn (fun _ : Unit => false) (fun _ : Unit => true) ∅ := by
    refine ⟨continuous_const, ?_⟩
    intro x hx
    simp at hx
  have heq : (fun _ : Unit => false) = (fun _ : Unit => true) :=
    (hunique _ hfalse).trans (hunique _ htrue).symm
  have : false = true := congrFun heq ()
  simp at this
