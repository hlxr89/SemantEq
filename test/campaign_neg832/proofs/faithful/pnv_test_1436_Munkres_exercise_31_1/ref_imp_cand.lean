import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_31_1_assumed {X : Type*} [TopologicalSpace X]
  (hX : RegularSpace X) (x y : X) (hxy : x ≠ y) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} [TopologicalSpace X] [T1Space X] (h : ∀ x y : X, IsClosed ({x} : Set X) ∧ IsClosed ({y} : Set X)) : RegularSpace X := by
  -- not proved: the antecedent requires RegularSpace X and therefore cannot establish regularity from the strictly weaker T1 hypotheses
  sorry
