import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {H K : Subgroup G} [hH : H.Normal] [hK : K.Normal] : (H ⊓ K).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_1_22a (G : Type*) [Group G] (H K : Subgroup G)
  [Normal H] [Normal K] :
  Normal (H ⊓ K) := by
  exact dummy_assumed
