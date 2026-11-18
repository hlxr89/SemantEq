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
theorem dummy {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (N : Subgroup G) [HN : N.Normal] (h : N.map φ = ⊤) : φ.range.Normal := by
  have hmap : (N.map φ).Normal := exercise_2_7_7_assumed φ N
  have himage_range : N.map φ = φ.range := by
    apply le_antisymm
    · exact Subgroup.map_le_range φ N
    · rw [h]
      exact le_top
  rw [← himage_range]
  exact hmap
