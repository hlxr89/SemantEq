import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (h : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have hprod : τ * σ = 1 := by
    ext x
    exact congrFun h2 x
  have hfix : ∀ x, τ x ≠ x → σ x = x := fun x hx => (h1 x).mpr hx
  obtain ⟨hτ, hσ⟩ := dummy_assumed τ σ hfix hprod
  exact ⟨hσ, hτ⟩
