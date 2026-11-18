import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {α : Type*} [Ring α] [IsDomain α] [CharZero α] (a : α) (n : ℕ) : a^n = a ↔ a = 1 ∨ n = 1 := sorry
