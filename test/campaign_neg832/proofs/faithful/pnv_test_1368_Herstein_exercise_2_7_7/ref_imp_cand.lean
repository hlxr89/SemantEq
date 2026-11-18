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
theorem dummy {G H : Type*} [Group G] [Group H] {N : Subgroup G} {f : G →* H} (hf : Function.Surjective f) (h : N.Normal) : (N.map f).Normal := by
  letI := h
  exact exercise_2_7_7_assumed f N
