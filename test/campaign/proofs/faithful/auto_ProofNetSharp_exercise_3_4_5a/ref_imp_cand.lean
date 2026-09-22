import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_4_5a_refs_assumed {G : Type*} [Group G]
  (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_5a {G : Type*} [Group G] (hG : IsSolvable G) (H : Subgroup G) :
    IsSolvable H := by
  letI : IsSolvable G := hG
  exact exercise_3_4_5a_refs_assumed H
