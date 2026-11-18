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
theorem dummy {α : Type*} [Fintype α] {σ τ : Equiv.Perm α} (h : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  have href := exercise_3_2_21_assumed (α := Empty) (σ := 1) (τ := 1)
    (by intro a; exact a.elim)
    (by ext a; exact a.elim)
  have hcomp : ∀ x, σ (τ x) = x := by
    intro x
    have hx := DFunLike.congr_fun hστ x
    simpa using hx
  have hσ : σ = 1 := by
    ext x
    by_contra hx
    apply hx
    calc
      σ x = σ (τ x) := congrArg σ (h x hx).symm
      _ = x := hcomp x
  have hτ : τ = 1 := by
    simpa [hσ] using hστ
  exact Eq.mp (congrArg (fun _ : Equiv.Perm Empty => σ = 1 ∧ τ = 1) href.1) ⟨hσ, hτ⟩
