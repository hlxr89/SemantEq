import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (hσ : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have hs : σ = 1 := by
    ext a
    by_contra ha
    have ht : τ a = a := of_not_not ((not_congr (h1 a)).mp ha)
    have hc := congrFun h2 a
    simp only [Function.comp_apply, id_eq] at hc
    exact ha (τ.injective (hc.trans ht.symm))
  constructor
  · exact hs
  · ext a
    have hc := congrFun h2 a
    simp only [Function.comp_apply, id_eq] at hc
    simpa [hs] using hc
