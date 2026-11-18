import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} (h : IsClosed (closure Aᶜ : Set X)) {f : X → Y} (hf : ContinuousOn f A) (g : X → Y) (hg : ContinuousOn g A) (hfg : Set.EqOn f g (closure Aᶜ)) : Set.EqOn f g A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_13
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {A : Set X} {f : X → Y} (hf : ContinuousOn f A)
  (g : X → Y) (g_con : ContinuousOn g (closure A))
  (gExt : ∀ x : A, g x = f x) :
  ∀ (g' : X → Y), (ContinuousOn g' (closure A) ∧ (∀ x : A, g' x = f x)) → (∀ x : closure A, g x = g' x) := by
  rintro g' ⟨g'_con, g'Ext⟩ x
  have hclosed : IsClosed {x ∈ closure A | g x = g' x} :=
    isClosed_closure.isClosed_eq g_con g'_con
  have hsub : A ⊆ {x ∈ closure A | g x = g' x} := by
    intro y hy
    exact ⟨subset_closure hy, (gExt ⟨y, hy⟩).trans (g'Ext ⟨y, hy⟩).symm⟩
  exact (closure_minimal hsub hclosed x.property).2
