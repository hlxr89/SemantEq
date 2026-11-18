import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {a b : G} (h1 : a * b = b * a) (h2 : a * b * a⁻¹ = b) : a = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have hτσ : τ * σ = 1 := by
    ext x
    exact congr_fun h2 x
  have hστ : σ * τ = 1 := mul_eq_one_comm.mp hτσ
  have hcomm : σ * τ = τ * σ := hστ.trans hτσ.symm
  have hconj : σ * τ * σ⁻¹ = τ := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hσ : σ = 1 := dummy_assumed hcomm hconj
  constructor
  · exact hσ
  · simpa [hσ] using hτσ
