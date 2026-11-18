import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (p : ℕ) [Fact (Nat.Prime p)] : (p - 1)/2 = ((Finset.range (p - 1)).filter (fun x : ℕ => x^2 ≡ 1 [MOD p])).card := sorry
