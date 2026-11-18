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
  intro g' hg' x
  have hfg : Set.EqOn (Set.restrict (closure A) g) (Set.restrict (closure A) g')
      (closure (Set.univ : Set (closure A))ᶜ) := by
    rw [compl_univ, closure_empty]
    exact Set.eqOn_empty _ _
  have heq := dummy_assumed (A := (Set.univ : Set (closure A))) isClosed_closure
    g_con.restrict.continuousOn (Set.restrict (closure A) g') hg'.1.restrict.continuousOn hfg
  exact heq (Set.mem_univ x)
