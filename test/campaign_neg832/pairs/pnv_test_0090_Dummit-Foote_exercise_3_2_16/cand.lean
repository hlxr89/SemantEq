import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {a : ℕ} {p : ℕ} [hp : Fact (Nat.Prime p)] : a ^ p ≡ a [MOD p] := sorry
