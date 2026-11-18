import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_7_7_assumed {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G G' : Type*} [Group G] [Group G'] (ϕ : G →* G') (hϕ : Function.Surjective ϕ) {N : Subgroup G} (hN : N.Normal) : (N.map ϕ).Normal := by
  letI := hN
  exact exercise_2_7_7_assumed ϕ N
