import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G H : Type*} [Group G] [Group H] {N : Subgroup G} {f : G →* H} (hf : Function.Surjective f) (h : N.Normal) : (N.map f).Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  -- not proved: the assumed statement requires surjectivity of φ, which is not a hypothesis and does not hold for an arbitrary group homomorphism
  sorry
