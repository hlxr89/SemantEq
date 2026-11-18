import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (hσ : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  have hσ_one : σ = 1 := by
    ext a
    by_contra ha
    have hτa : τ a = a := not_ne_iff.mp (mt (h1 a).mpr ha)
    have hcomp := congrFun h2 a
    apply ha
    change σ a = a
    apply τ.injective
    simpa [hτa] using hcomp
  have hτ_one : τ = 1 := by
    ext a
    have hcomp := congrFun h2 a
    simpa [hσ_one] using hcomp
  exact ⟨hσ_one, hτ_one⟩
