import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} (h : Fact p.Prime) {P : Sylow p G} (φ : G ≃* G) : φ '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro φ
  apply SetLike.coe_injective
  rw [Subgroup.coe_map]
  exact dummy_assumed ⟨hp⟩ φ
