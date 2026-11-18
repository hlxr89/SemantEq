import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} (h : Fact p.Prime) {P : Sylow p G} (φ : G ≃* G) : φ '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  ext x
  change x ∈ φ '' (P : Set G) ↔ x ∈ (P : Set G)
  rw [dummy_assumed (h := ⟨hp⟩) φ]
