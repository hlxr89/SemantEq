import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] [CompactSpace X]: ∀ (f : X → X), ∀ (x y : X), dist (f x) (f y) = dist x y → Isometry f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  letI : Subsingleton X :=
    ⟨fun a b =>
      eq_of_dist_eq_zero <|
        ((dummy_assumed (fun _ : X => a) a a rfl).dist_eq a b).symm.trans (dist_self a)⟩
  have hbij : Bijective f :=
    ⟨hf.injective, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  have hopen : IsOpenMap f := by
    let e : X ≃ₜ X :=
      { toFun := f
        invFun := f
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        continuous_toFun := hf.continuous
        continuous_invFun := hf.continuous }
    exact e.isOpenMap
  exact ⟨hf.continuous, hbij, hopen⟩
