import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The input preambles have no local definitions. These transparent aliases
-- provide a common universe for the universe-polymorphism bridge.
universe u₁ u₂

private abbrev CommonLiftLeft (X : Type u₁) (Y : Type u₂) :=
  ULift.{max u₁ u₂, u₁} X

private abbrev CommonLiftRight (X : Type u₁) (Y : Type u₂) :=
  ULift.{max u₁ u₂, u₂} Y

-- ===== assumed statement (antecedent) =====
theorem exercise_22_5_assumed {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (h : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  have h_restriction := exercise_22_5_assumed p h A hA Set.univ isOpen_univ
  rw [show p '' A = (p ∘ Subtype.val : A → Y) '' Set.univ by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.property, rfl⟩]
  exact h_restriction
