import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (G' : Type*) [Group G'] (f : G →* G') (hf : Function.Surjective f) (h1 : IsSolvable G) : IsSolvable G' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4_5b {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  exact dummy_assumed G (G ⧸ H) (QuotientGroup.mk' H)
    (QuotientGroup.mk'_surjective H) (inferInstance : IsSolvable G)
