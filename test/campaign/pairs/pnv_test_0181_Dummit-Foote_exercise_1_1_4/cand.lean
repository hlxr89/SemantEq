import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℕ) : ∀ x y z : (ZMod n), ((x : ZMod n) * y) * z = x * (y * z) := sorry
