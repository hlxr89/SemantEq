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
  have hs : σ = 1 := by
    ext x
    by_contra hx
    have ht : τ x = x := by
      by_contra htx
      exact hx ((h1 x).2 htx)
    apply hx
    apply τ.injective
    calc
      τ (σ x) = x := by simpa only [Function.comp_apply, id_eq] using congrFun h2 x
      _ = τ x := ht.symm
  constructor
  · exact hs
  · ext x
    have hc : τ (σ x) = x := by
      simpa only [Function.comp_apply, id_eq] using congrFun h2 x
    simpa [hs] using hc
