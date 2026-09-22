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
theorem dummy {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (h : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  have h_restriction := exercise_22_5_assumed p h A hA
  convert h_restriction Set.univ isOpen_univ using 1 <;>
    ext y <;> simp
