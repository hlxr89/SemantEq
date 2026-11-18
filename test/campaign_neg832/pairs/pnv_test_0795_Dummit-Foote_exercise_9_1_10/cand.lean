import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [CommRing R] [DecidableEq R] (hR : ∀ n : ℕ, ∃ x : R, x ≠ 0 ∧ ∀ m : ℕ, m < n → x ^ (n + 1) ≠ 0) : ∃ (I : Ideal R) (H : I.IsPrime), ∀ J : Ideal R, J.IsPrime → I ≤ J → J = I := sorry
