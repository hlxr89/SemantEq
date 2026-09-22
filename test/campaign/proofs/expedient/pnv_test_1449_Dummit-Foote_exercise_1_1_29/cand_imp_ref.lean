import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {A B : Type*} [Group A] [Group B] : (∀ a₁ a₂ : A × B, a₁ * a₂ = a₂ * a₁) ↔ (∀ a₁ a₂ : A, a₁ * a₂ = a₂ * a₁) ∧ (∀ b₁ b₂ : B, b₁ * b₂ = b₂ * b₁) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_29 {A B : Type*} [Group A] [Group B] :
  (∀ x y : A × B, x*y = y*x) ↔ (∀ x y : A, x*y = y*x) ∧
  (∀ x y : B, x*y = y*x) := by
  simpa using (dummy_assumed (A := A) (B := B))
