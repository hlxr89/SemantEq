import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

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
  letI : MetricSpace (α ⊕ α) := Metric.metricSpaceSum
  let F : α ⊕ α → β := Sum.elim f g
  let G : α ⊕ α → β := Sum.elim g f
  have hF : Continuous F := by
    rw [continuous_sum_dom]
    simpa [F, Function.comp_def] using And.intro h₁ h₂
  have hG : Continuous G := by
    rw [continuous_sum_dom]
    simpa [G, Function.comp_def] using And.intro h₂ h₁
  have hImage : F '' Set.univ = G '' Set.univ := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      cases x with
      | inl x => exact ⟨Sum.inr x, Set.mem_univ _, by simp [F, G]⟩
      | inr x => exact ⟨Sum.inl x, Set.mem_univ _, by simp [F, G]⟩
    · rintro ⟨x, -, rfl⟩
      cases x with
      | inl x => exact ⟨Sum.inr x, Set.mem_univ _, by simp [F, G]⟩
      | inr x => exact ⟨Sum.inl x, Set.mem_univ _, by simp [F, G]⟩
  have hPointwise := dummy_assumed (X := α ⊕ α) (Y := β)
    (f := F) (g := G) (P := Set.univ) hImage hF hG isClosed_univ dense_univ
  apply funext
  intro x
  simpa [F, G] using hPointwise (Sum.inl x) (Set.mem_univ _)
