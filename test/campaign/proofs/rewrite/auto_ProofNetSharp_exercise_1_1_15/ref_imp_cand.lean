import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_15_refs_assumed {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_15 {G : Type*} [Group G] (l : List G) :
    l.prod⁻¹ = (l.reverse.map fun a => a⁻¹).prod :=
  by
    exact exercise_1_1_15_refs_assumed l
