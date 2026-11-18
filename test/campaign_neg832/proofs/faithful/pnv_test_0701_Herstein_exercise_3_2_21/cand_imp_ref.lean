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
  apply dummy_assumed
  · intro x hx
    apply not_ne_iff.mp
    intro hτx
    exact hx ((h1 x).2 hτx)
  · ext x
    apply τ.injective
    have hx := congrFun h2 (τ x)
    simpa [Function.comp_apply] using hx
