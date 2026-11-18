import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_5_52_assumed {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] [Fintype G] (φ : G →* G) (hφ : ∀ (x : G), x ≠ 1 → φ x = x⁻¹) : ∀ (y : G), φ y = y⁻¹ := by
  intro y
  have hall : ∀ x : G, φ x = x⁻¹ := by
    intro x
    by_cases hx : x = 1
    · subst x
      simpa only [map_one, inv_one]
    · exact hφ x hx
  let ψ : G ≃* G :=
    { toFun := φ
      invFun := fun x => x⁻¹
      left_inv := fun x => by
        rw [hall x]
        simp only [inv_inv]
      right_inv := fun x => by
        rw [hall x⁻¹]
        simp only [inv_inv]
      map_mul' := φ.map_mul }
  have hψ : ∀ x ∈ (Finset.univ : Finset G), ψ x = x⁻¹ := by
    intro x hx
    exact hall x
  have hcard : (0.75 : ℚ) * card G ≤ card (Finset.univ : Finset G) := by
    rw [Fintype.card_coe, Finset.card_univ]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by norm_num)
  exact (exercise_2_5_52_assumed ψ hψ hcard).1 y
