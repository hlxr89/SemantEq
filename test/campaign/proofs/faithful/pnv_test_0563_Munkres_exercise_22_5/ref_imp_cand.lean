import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_22_5_assumed {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (h : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  have hopen := exercise_22_5_assumed p h A hA Set.univ isOpen_univ
  have himage : (p ∘ Subtype.val : A → Y) '' Set.univ = p '' A := by
    ext y
    constructor
    · rintro ⟨a, -, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  rw [himage] at hopen
  exact hopen
