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
  intro g' hg' x
  let emptyMap : (∅ : Set (closure A)) → Y := fun z => z.property.elim
  have hempty : Continuous emptyMap :=
    continuous_iff_continuousAt.mpr fun z => z.property.elim
  obtain ⟨u, hu, hu_unique⟩ :=
    dummy_assumed (X := closure A) (Y := Y) inferInstance (A := ∅)
      isClosed_empty (f := emptyMap) hempty
  have hg : Continuous (fun x : closure A => g x) :=
    continuousOn_iff_continuous_restrict.mp g_con
  have hg'con : Continuous (fun x : closure A => g' x) :=
    continuousOn_iff_continuous_restrict.mp hg'.1
  have hgu : (fun x : closure A => g x) = u :=
    hu_unique (fun x : closure A => g x) ⟨fun z => z.property.elim, hg⟩
  have hg'u : (fun x : closure A => g' x) = u :=
    hu_unique (fun x : closure A => g' x) ⟨fun z => z.property.elim, hg'con⟩
  exact congrFun (hgu.trans hg'u.symm) x
