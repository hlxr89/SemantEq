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
theorem dummy {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (hσ : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  have hs : σ = 1 := by
    ext x
    by_contra hx
    have ht : τ x = x := hσ x hx
    have hp := congrArg (fun p : Equiv.Perm α => p x) hστ
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one,
      id_eq] at hp
    rw [ht] at hp
    exact hx hp
  subst σ
  simpa using hστ
