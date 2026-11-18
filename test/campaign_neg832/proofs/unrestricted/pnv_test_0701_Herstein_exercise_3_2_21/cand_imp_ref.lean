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
  have hσ : σ = 1 := by
    ext x
    by_contra hx
    have hτx : τ x = x := by
      by_contra hτx
      exact hx ((h1 x).mpr hτx)
    have hσx : σ x = x := τ.injective (by
      calc
        τ (σ x) = x := congrFun h2 x
        _ = τ x := hτx.symm)
    exact hx (by simpa using hσx)
  have hτ : τ = 1 := by
    ext x
    have hx := congrFun h2 x
    simpa [hσ] using hx
  exact ⟨hσ, hτ⟩
