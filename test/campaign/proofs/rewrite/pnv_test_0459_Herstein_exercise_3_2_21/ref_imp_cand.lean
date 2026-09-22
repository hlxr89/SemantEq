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
  have h_mul_eq_one' : τ * σ = 1 :=
    mul_eq_one_comm.mp h_mul_eq_one
  have h2 : τ ∘ σ = id := by
    funext x
    have hx := congrArg (fun p : Equiv.Perm α => p x) h_mul_eq_one'
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      Function.comp_apply, id_eq] using hx
  letI : IsEmpty α := ⟨fun x => by
    rcases (h x).1 with hσ | hτ
    · have hτ' : τ x = x := by
        have hx := congrFun h2 x
        simpa only [Function.comp_apply, id_eq, hσ] using hx
      exact (h x).2 ⟨hσ, hτ'⟩
    · have hσ' : σ x = x := by
        have hx := congrArg (fun p : Equiv.Perm α => p x) h_mul_eq_one
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hτ] using hx
      exact (h x).2 ⟨hσ', hτ⟩⟩
  letI : Fintype α := Fintype.ofFinite α
  have h1 : ∀ a : α, σ a = a ↔ τ a ≠ a := fun a => by
    constructor
    · intro hσ hτ
      exact (h a).2 ⟨hσ, hτ⟩
    · intro hτ
      exact (h a).1.resolve_right hτ
  exact exercise_3_2_21_assumed h1 h2
