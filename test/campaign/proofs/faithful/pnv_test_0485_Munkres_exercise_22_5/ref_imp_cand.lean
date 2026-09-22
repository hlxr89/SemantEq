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
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hf : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  have h := exercise_22_5_assumed p hf A hA (Set.univ : Set A) isOpen_univ
  rw [show (p ∘ Subtype.val : A → Y) '' Set.univ = p '' A by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩] at h
  exact h
