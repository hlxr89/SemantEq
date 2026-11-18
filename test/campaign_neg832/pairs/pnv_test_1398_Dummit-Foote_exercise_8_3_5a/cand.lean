import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {n : ℤ} (hn₁ : n > 3) (hn₂ : Nat.Prime (Int.natAbs n)) (hn₃ : ¬(∃ k, k ^ 2 = n)) (a : ℤ√(-n)) (ha₁ : a ≠ 0) (ha₂ : a.norm < n) : Irreducible a := sorry
