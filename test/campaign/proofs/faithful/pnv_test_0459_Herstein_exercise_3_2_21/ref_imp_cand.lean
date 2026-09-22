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
  have hτ_inv : τ = σ⁻¹ := by
    exact eq_inv_of_mul_eq_one_right h_mul_eq_one
  have h_empty : IsEmpty α := by
    refine ⟨fun x => ?_⟩
    have hfix : σ x = x ↔ τ x = x := by
      rw [hτ_inv]
      constructor
      · intro hs
        exact (Equiv.symm_apply_eq σ).2 hs.symm
      · intro ht
        exact ((Equiv.symm_apply_eq σ).1 ht).symm
    rcases (h x).1 with hs | ht
    · exact (h x).2 ⟨hs, hfix.mp hs⟩
    · exact (h x).2 ⟨hfix.mpr ht, ht⟩
  letI : Fintype α := Fintype.ofFinite α
  apply exercise_3_2_21_assumed
  · intro x
    exact (h_empty.false x).elim
  · funext x
    exact (h_empty.false x).elim
