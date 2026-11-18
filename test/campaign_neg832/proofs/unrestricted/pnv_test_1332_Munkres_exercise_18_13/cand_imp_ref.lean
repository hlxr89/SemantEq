import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} (hA : IsClosed A) {f : X → Y} (hf : ContinuousOn f A) {g₁ g₂ : X → Y} (hg₁ : ContinuousOn g₁ (closure A)) (hg₂ : ContinuousOn g₂ (closure A)) (hgf₁ : EqOn g₁ f A) (hgf₂ : EqOn g₂ f A) : EqOn g₁ g₂ (closure A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_13
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {A : Set X} {f : X → Y} (hf : ContinuousOn f A)
  (g : X → Y) (g_con : ContinuousOn g (closure A))
  (gExt : ∀ x : A, g x = f x) :
  ∀ (g' : X → Y), (ContinuousOn g' (closure A) ∧ (∀ x : A, g' x = f x)) → (∀ x : closure A, g x = g' x) := by
  intro g' hg' x
  exact Set.EqOn.of_subset_closure
    (fun y hy ↦ (gExt ⟨y, hy⟩).trans (hg'.2 ⟨y, hy⟩).symm)
    g_con hg'.1 subset_closure Subset.rfl x.property
