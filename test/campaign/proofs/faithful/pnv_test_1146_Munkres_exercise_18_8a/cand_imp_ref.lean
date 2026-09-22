import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) [Preorder Y] [LocallyFiniteOrder Y] : IsClosed {x : X | f x ≤ g x} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_8a {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x} := by
  let p : X → Prop := fun x ↦ f x ≤ g x
  let b : X → Fin 2 := fun x ↦ if p x then 1 else 0
  letI : TopologicalSpace (Fin 2) := ⊤
  have hb : Continuous b := continuous_top
  have ht : Continuous (fun _ : X ↦ (1 : Fin 2)) := continuous_const
  have hclosed : IsClosed {x : X | (fun _ : X ↦ (1 : Fin 2)) x ≤ b x} :=
    dummy_assumed ht hb
  have heq : {x : X | (fun _ : X ↦ (1 : Fin 2)) x ≤ b x} =
      {x : X | f x ≤ g x} := by
    ext x
    by_cases h : f x ≤ g x <;> simp [b, p, h]
  exact heq ▸ hclosed
