import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Fact (Prime p)) (hp1 : p % 4 = 1) (hp3 : p ≠ 3) (a : ℤ) (ha : a.gcd p = 1) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := sorry
