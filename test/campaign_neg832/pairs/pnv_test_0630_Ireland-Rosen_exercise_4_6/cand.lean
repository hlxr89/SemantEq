import Mathlib

open Real
open scoped BigOperators

theorem dummy {p n : ℕ} (hp : p = 2^n + 1) (hfp : Nat.Prime p) : IsPrimitiveRoot 3 p := sorry
