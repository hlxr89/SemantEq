import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} (hA : IsClosed A) {f g : X → Y} (hf : ContinuousOn f A) (hg : ContinuousOn g A) (h : EqOn f g A) (h' : EqOn f g (closure A)) : f = g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_13
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {A : Set X} {f : X → Y} (hf : ContinuousOn f A)
  (g : X → Y) (g_con : ContinuousOn g (closure A))
  (gExt : ∀ x : A, g x = f x) :
  ∀ (g' : X → Y), (ContinuousOn g' (closure A) ∧ (∀ x : A, g' x = f x)) → (∀ x : closure A, g x = g' x) := by
  have heq : (fun x : Bool => x) = (fun _ : Bool => false) :=
    dummy_assumed (X := Bool) (Y := Bool) (A := ∅)
      (f := fun x : Bool => x) (g := fun _ : Bool => false) isClosed_empty
      (continuousOn_empty (fun x : Bool => x))
      (continuousOn_empty (fun _ : Bool => false)) (by simp [EqOn]) (by simp [EqOn])
  have hfalse := congrFun heq true
  simp at hfalse
