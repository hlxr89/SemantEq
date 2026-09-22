import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_4_5a_assumed {G : Type*} [Group G] (hG : IsSolvable G) (H : Subgroup G) :
    IsSolvable H := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_5a_refs {G : Type*} [Group G]
  (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
by
  exact exercise_3_4_5a_assumed (inferInstance : IsSolvable G) H
