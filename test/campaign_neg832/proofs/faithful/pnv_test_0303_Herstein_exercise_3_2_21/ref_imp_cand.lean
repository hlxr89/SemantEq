import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_2_21_assumed {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (h : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  have h_transport := exercise_3_2_21_assumed
    (α := Empty) (σ := 1) (τ := 1)
    (by intro a; exact a.elim)
    (by rfl)
  have hσ : σ = 1 := by
    ext x
    by_contra hx
    have hτx : τ x = x := h x hx
    have hx' := Equiv.congr_fun hστ x
    simp [hτx] at hx'
    exact hx hx'
  have hτ : τ = 1 := by
    rw [hσ] at hστ
    simpa using hστ
  cases h_transport.1
  exact ⟨hσ, hτ⟩
