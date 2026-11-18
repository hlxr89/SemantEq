import Mathlib

open Real
open scoped BigOperators

theorem dummy {n : ℕ} {p : ℕ} (hp : p = 2^n + 1) (hprime : Nat.Prime p) : IsPrimitiveRoot 3 p := sorry
