import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : p = 4 * t + 1) (a : ℤ) (ha : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := sorry
