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
theorem dummy {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (hφ : Function.Surjective φ) (N : Subgroup G) (hN : N ≤ center G) : φ '' N ≤ center G' := by
  rintro _ ⟨n, hn, rfl⟩
  rw [Semigroup.mem_center_iff]
  intro y
  obtain ⟨g, rfl⟩ := hφ y
  simpa only [map_mul] using congrArg φ (Semigroup.mem_center_iff.mp (hN hn) g)
