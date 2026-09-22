import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_29 {A B : Type*} [Group A] [Group B] :
  (∀ x y : A × B, x*y = y*x) ↔ (∀ x y : A, x*y = y*x) ∧
  (∀ x y : B, x*y = y*x) := sorry
