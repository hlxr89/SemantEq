import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [DecidableEq α] [Fintype α] {σ τ : Equiv.Perm α} (hστ : ∀ x, σ x ≠ x → τ x = x) (hσττ : ∀ x, τ x ≠ x → σ x = x) : σ = 1 ∧ τ = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  classical
  apply dummy_assumed
  · intro x hσ
    exact Classical.byContradiction fun hτ => hσ ((h1 x).mpr hτ)
  · intro x hτ
    exact (h1 x).mpr hτ
