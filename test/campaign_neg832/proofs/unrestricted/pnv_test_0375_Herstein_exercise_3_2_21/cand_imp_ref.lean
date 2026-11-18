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
  have hσ : σ = 1 := by
    ext a
    change σ a = a
    by_contra hsa
    have hta : τ a = a := by
      by_contra hta
      exact hsa ((h1 a).mpr hta)
    apply hsa
    apply τ.injective
    have hcomp : τ (σ a) = a := by
      simpa [Function.comp_def] using congrFun h2 a
    exact hcomp.trans hta.symm
  constructor
  · exact hσ
  · ext a
    simpa [Function.comp_def, hσ] using congrFun h2 a
