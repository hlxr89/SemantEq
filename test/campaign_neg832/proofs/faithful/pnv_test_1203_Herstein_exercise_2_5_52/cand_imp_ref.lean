import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : Finite G) (f : G ≃* G) (hf : ∀ g : G, g ∈ f ⁻¹' {g⁻¹} → g ∈ {x : G | x⁻¹ = x}) : ∀ g : G, f g = g⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_5_52 {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  have h_inv : ∀ g : G, g = g⁻¹ :=
    dummy_assumed (G := G) (by infer_instance) (MulEquiv.refl G) (by
      intro g hg
      change g⁻¹ = g
      change g = g⁻¹ at hg
      exact hg.symm)
  have hφ : ∀ g : G, φ g = g⁻¹ :=
    dummy_assumed (G := G) (by infer_instance) φ (by
      intro g hg
      change g⁻¹ = g
      exact (h_inv g).symm)
  refine ⟨hφ, ?_⟩
  intro x y
  calc
    x * y = (x * y)⁻¹ := h_inv (x * y)
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [← h_inv y, ← h_inv x]
