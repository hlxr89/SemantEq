import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} {σ τ : Equiv.Perm α} (h : ∀ x : α, σ x = τ x) (hστ : σ * τ = 1) : σ = τ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have haFalse : ∀ a : α, False := by
    intro a
    have hτσ : τ (σ a) = a := by
      simpa using congrFun h2 a
    have hσ : σ a ≠ a := by
      intro hσ
      have hτne : τ a ≠ a := (h1 a).mp hσ
      apply hτne
      simpa [hσ] using hτσ
    have hτ : τ a = a := by
      apply not_ne_iff.mp
      intro hτne
      exact hσ ((h1 a).mpr hτne)
    apply hσ
    apply τ.injective
    calc
      τ (σ a) = a := hτσ
      _ = τ a := hτ.symm
  constructor <;> ext a <;> exact (haFalse a).elim
