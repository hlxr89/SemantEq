import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G G' : Type*} [Group G] [Group G'] {ϕ : G →* G'} (hϕ : Function.Surjective ϕ) {N : Subgroup G} (hN : N.Normal) : (N.map ϕ).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  -- not proved: the assumed statement requires surjectivity, but an arbitrary group homomorphism need not be surjective and the claimed image need not be normal
  sorry
