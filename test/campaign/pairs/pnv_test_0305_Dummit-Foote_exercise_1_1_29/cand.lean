import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {A B : Type*} [Group A] [Group B] : (∀ x y : A × B, x * y = y * x) ↔ (∀ a1 a2 : A, a1 * a2 = a2 * a1) ∧ (∀ b1 b2 : B, b1 * b2 = b2 * b1) := sorry
