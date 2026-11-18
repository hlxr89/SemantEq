import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [Fintype α] {σ τ : Equiv.Perm α} (h : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have h : ∀ x, σ x ≠ x → τ x = x := by
    intro x hσ
    apply not_ne_iff.mp
    intro hτ
    exact hσ ((h1 x).mpr hτ)
  have hτσ : τ * σ = 1 := by
    ext x
    exact congrFun h2 x
  have hστ : σ * τ = 1 := mul_eq_one_comm.mp hτσ
  exact dummy_assumed h hστ
