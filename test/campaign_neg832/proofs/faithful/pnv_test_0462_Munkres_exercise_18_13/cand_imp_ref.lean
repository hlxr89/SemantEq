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
  intro g' hg'
  let gc : closure A → Y := (closure A).restrict g
  let g'c : closure A → Y := (closure A).restrict g'
  let e : (∅ : Set (closure A)) → Y := (∅ : Set (closure A)).restrict gc
  have hgc : Continuous gc := g_con.restrict
  have hg'c : Continuous g'c := hg'.1.restrict
  have he : Continuous e := hgc.comp continuous_subtype_val
  rcases dummy_assumed (X := closure A) (Y := Y) (inferInstance) (A := ∅)
      isClosed_empty (f := e) he with ⟨u, hu, huniq⟩
  have hgc_prop : (∀ a : (∅ : Set (closure A)), gc a = e a) ∧ Continuous gc := by
    constructor
    · intro a
      exact a.property.elim
    · exact hgc
  have hg'c_prop : (∀ a : (∅ : Set (closure A)), g'c a = e a) ∧ Continuous g'c := by
    constructor
    · intro a
      exact a.property.elim
    · exact hg'c
  have hgc_eq : gc = u := huniq gc hgc_prop
  have hg'c_eq : g'c = u := huniq g'c hg'c_prop
  intro x
  exact congrFun (hgc_eq.trans hg'c_eq.symm) x
