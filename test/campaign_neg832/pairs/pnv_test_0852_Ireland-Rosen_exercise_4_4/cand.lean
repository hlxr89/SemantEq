import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} [hp : Fact (Nat.Prime p)] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := sorry
