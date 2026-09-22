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
  have hcomp (x : α) : σ (τ x) = x := by
    simpa [Equiv.Perm.mul_apply] using congrArg (fun p : Equiv.Perm α => p x) h_mul_eq_one
  haveI : IsEmpty α :=
    ⟨fun x => by
      have heq : σ x = x ↔ τ x = x := by
        constructor
        · intro hs
          exact σ.injective (by simpa [hs] using hcomp x)
        · intro ht
          simpa [ht] using hcomp x
      rcases (h x).1 with hs | ht
      · exact (h x).2 ⟨hs, heq.mp hs⟩
      · exact (h x).2 ⟨heq.mpr ht, ht⟩⟩
  constructor <;> ext x <;> exact isEmptyElim x
