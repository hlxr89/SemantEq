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
theorem dummy {G G' : Type*} [Group G] [Group G'] {N : Subgroup G} (φ : G →* G') (hN : N.Normal) : (φ.ker.map φ).Normal := by
  have himage : φ.ker.map φ = ⊥ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      subst y
      exact ⟨1, by simp⟩
  rw [himage]
  infer_instance
