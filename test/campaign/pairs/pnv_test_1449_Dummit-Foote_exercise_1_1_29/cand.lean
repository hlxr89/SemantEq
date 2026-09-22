import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {A B : Type*} [Group A] [Group B] : (∀ a₁ a₂ : A × B, a₁ * a₂ = a₂ * a₁) ↔ (∀ a₁ a₂ : A, a₁ * a₂ = a₂ * a₁) ∧ (∀ b₁ b₂ : B, b₁ * b₂ = b₂ * b₁) := sorry
