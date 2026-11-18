import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [DecidableEq α] {σ τ : Equiv.Perm α} (h : ∀ x, σ x ≠ τ x) (h' : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  classical
  apply dummy_assumed
  · intro x heq
    have hx := h1 x
    rw [← heq] at hx
    by_cases hs : σ x = x
    · exact (hx.mp hs) hs
    · exact hs (hx.mpr hs)
  · have hmul : τ * σ = 1 := by
      ext x
      exact congrFun h2 x
    exact mul_eq_one_comm.mp hmul
