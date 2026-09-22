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
theorem dummy {α : Type*} (σ τ : Equiv.Perm α) (h : ∀ x : α, (σ x = x ∨ τ x = x) ∧ ¬(σ x = x ∧ τ x = x)) (h_mul_eq_one : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  have h_mul_eq_one' : τ * σ = 1 := mul_eq_one_comm.mp h_mul_eq_one
  have hinv (x : α) : τ (σ x) = x := by
    simpa using Equiv.congr_fun h_mul_eq_one' x
  have hfixed (x : α) : σ x = x ↔ τ x = x := by
    constructor
    · intro hs
      calc
        τ x = τ (σ x) := congrArg τ hs.symm
        _ = x := hinv x
    · intro ht
      apply τ.injective
      rw [ht]
      exact hinv x
  have hempty (x : α) : False := by
    rcases (h x).1 with hs | ht
    · exact (h x).2 ⟨hs, (hfixed x).mp hs⟩
    · exact (h x).2 ⟨(hfixed x).mpr ht, ht⟩
  constructor <;> ext x <;> exact False.elim (hempty x)
