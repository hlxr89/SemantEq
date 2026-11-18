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
  have bad := dummy_assumed (α := Fin 3)
    (σ := Equiv.swap 0 1 * Equiv.swap 1 2)
    (τ := Equiv.swap 1 2 * Equiv.swap 0 1)
    (by native_decide) (by native_decide)
  have hn : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠ 1 := by
    native_decide
  exact (hn bad.1).elim
