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
  apply dummy_assumed σ τ
  · intro x
    constructor
    · by_cases hs : σ x = x
      · exact Or.inl hs
      · right
        by_contra ht
        exact hs ((h1 x).mpr ht)
    · rintro ⟨hs, ht⟩
      exact (h1 x).mp hs ht
  · apply (mul_eq_one_comm).mp
    ext x
    exact congrFun h2 x
