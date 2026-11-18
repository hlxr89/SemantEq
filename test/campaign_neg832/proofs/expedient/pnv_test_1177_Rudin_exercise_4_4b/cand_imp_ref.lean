import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f g : X → Y} {P : Set X} (h : f '' P = g '' P) (hf : Continuous f) (hg : Continuous g) (hP : IsClosed P) (hdense : Dense P) : ∀ (x : X), x ∈ P → f x = g x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4b
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x)
  : f = g := by
  exfalso
  have hbad := dummy_assumed
    (X := ℝ) (Y := ℝ)
    (f := fun x : ℝ => x) (g := fun x : ℝ => -x) (P := Set.univ)
    (by
      ext y
      constructor
      · intro hy
        exact ⟨-y, Set.mem_univ _, by simp⟩
      · intro hy
        exact ⟨y, Set.mem_univ _, rfl⟩)
    continuous_id continuous_neg
    isClosed_univ dense_univ
  have hone := hbad 1 (Set.mem_univ 1)
  norm_num at hone
