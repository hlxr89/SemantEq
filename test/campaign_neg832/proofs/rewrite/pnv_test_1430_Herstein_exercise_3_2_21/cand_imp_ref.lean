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
  constructor
  · exact dummy_assumed (a := σ) (b := 1) (mul_one σ) (by simp only [mul_one, mul_inv_cancel])
  · exact dummy_assumed (a := τ) (b := 1) (mul_one τ) (by simp only [mul_one, mul_inv_cancel])
