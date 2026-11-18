import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {q : ℕ} (hq : q % 4 = 3) (hq_prime : Nat.Prime q) : IsField (ZMod (Int.natAbs q)) := sorry
