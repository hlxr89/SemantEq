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
theorem dummy {α : Type*} [Fintype α] (σ τ : Equiv.Perm α) (hσ : ∀ x, σ x ≠ x → τ x = x) (hστ : σ * τ = 1) : σ = 1 ∧ τ = 1 := by
  -- non-rewrite step: the candidate hypotheses imply the conclusion directly;
  -- they cannot supply the reference statement's incompatible fixed-point iff.
  have hσ1 : σ = 1 := by
    ext x
    by_contra hx
    have hτx : τ x = x := hσ x hx
    have hprod := DFunLike.congr_fun hστ x
    change σ (τ x) = x at hprod
    rw [hτx] at hprod
    exact hx hprod
  have hτ1 : τ = 1 := by
    rw [hσ1, one_mul] at hστ
    exact hστ
  exact ⟨hσ1, hτ1⟩
