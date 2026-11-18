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
theorem dummy {α : Type*} [DecidableEq α] [Fintype α] {σ τ : Equiv.Perm α} (hστ : ∀ x, σ x ≠ x → τ x = x) (hσττ : ∀ x, τ x ≠ x → σ x = x) : σ = 1 ∧ τ = 1 := by
  -- not proved: the candidate permits nontrivial permutations with disjoint supports, so it does not follow from the reference statement
  sorry
