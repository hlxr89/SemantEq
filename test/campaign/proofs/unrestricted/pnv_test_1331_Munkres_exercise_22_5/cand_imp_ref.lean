import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (h : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩
  have hopen : IsOpen (p '' (V ∩ A)) := hp (V ∩ A) (hV.inter hA)
  convert hopen using 1 <;>
    ext y <;> simp [and_assoc]
