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
  have hc (x : α) : τ (σ x) = x := by
    have hx := congrFun h2 x
    simpa using hx
  have hs (x : α) : σ x = x := by
    by_contra hx
    have ht : τ x = x := by
      by_contra htx
      exact hx ((h1 x).mpr htx)
    exact hx (τ.injective (by
      calc
        τ (σ x) = x := hc x
        _ = τ x := ht.symm))
  constructor <;> ext x
  · simpa using hs x
  · simpa [hs x] using hc x
