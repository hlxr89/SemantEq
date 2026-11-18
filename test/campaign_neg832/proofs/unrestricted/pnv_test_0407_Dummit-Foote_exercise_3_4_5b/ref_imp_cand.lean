import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_4_5b_assumed {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G H : Type*} [Group G] [Group H] [hG : IsSolvable G] (f : G →* H) : IsSolvable H := by
  -- not proved: the claim is false without a surjectivity hypothesis on f
  sorry
