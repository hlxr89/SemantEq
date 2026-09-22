import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} (σ τ : Equiv.Perm α) (h : ∀ x : α, (σ x = x ∨ τ x = x) ∧ ¬(σ x = x ∧ τ x = x)) (h_mul_eq_one : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have hcomp (x : α) : τ (σ x) = x := congrFun h2 x
  haveI : IsEmpty α :=
    ⟨fun x => by
      have heq : σ x = x ↔ τ x = x := by
        constructor
        · intro hs
          simpa [hs] using hcomp x
        · intro ht
          exact τ.injective (by simpa [ht] using hcomp x)
      by_cases hs : σ x = x
      · exact (h1 x).mp hs (heq.mp hs)
      · have ht : τ x ≠ x := fun htx => hs (heq.mpr htx)
        exact hs ((h1 x).mpr ht)⟩
  constructor <;> ext x <;> exact isEmptyElim x
