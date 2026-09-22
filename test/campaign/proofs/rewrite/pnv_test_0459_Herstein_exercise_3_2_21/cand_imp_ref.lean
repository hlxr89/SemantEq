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
  have h : ∀ x : α, (σ x = x ∨ τ x = x) ∧ ¬(σ x = x ∧ τ x = x) := fun x => by
    constructor
    · exact Classical.or_iff_not_imp_right.mpr (h1 x).mpr
    · intro hx
      exact (h1 x).mp hx.1 hx.2
  have h_mul_eq_one' : τ * σ = 1 := by
    apply Equiv.Perm.ext
    intro x
    have hx := congrFun h2 x
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      Function.comp_apply, id_eq] using hx
  have h_mul_eq_one : σ * τ = 1 :=
    mul_eq_one_comm.mpr h_mul_eq_one'
  exact dummy_assumed σ τ h h_mul_eq_one
