import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (φ : MonoidHom G G) (t : Finset G) (ht : t.card = Fintype.card G / 4) (h : ∀ x ∈ t, φ x = x⁻¹) : ∀ x : G, φ x = x⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_5_52 {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  have hquarter : card G / 4 ≤ I.card := by
    norm_num at hI1
    have hmulQ : (card G : ℚ) ≤ 4 * (I.card : ℚ) := by linarith
    have hmul : card G ≤ 4 * I.card := by exact_mod_cast hmulQ
    exact Nat.div_le_of_le_mul hmul
  obtain ⟨t, htI, ht⟩ := Finset.exists_subset_card_eq hquarter
  have hall : ∀ x : G, φ x = x⁻¹ :=
    dummy_assumed φ.toMonoidHom t ht (fun x hx ↦ hI x (htI hx))
  refine ⟨hall, ?_⟩
  intro x y
  calc
    x * y = ((x * y)⁻¹)⁻¹ := by simp
    _ = (φ (x * y))⁻¹ := by rw [hall]
    _ = (φ x * φ y)⁻¹ := by rw [map_mul]
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [hall, hall]
    _ = y * x := by simp
