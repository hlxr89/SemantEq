import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (N : Subgroup G) [HN : N.Normal] (h : N.map φ = ⊤) : φ.range.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  -- not proved: the candidate only treats the case N.map φ = ⊤, while the reference claims normality of an arbitrary image
  sorry
