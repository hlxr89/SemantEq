import Mathlib

open Real
open scoped BigOperators

theorem dummy (p : ℕ) [Fact (Nat.Prime p)] (hp : (p : ℤ) = 4*t+1) (a : ℤ) (hap : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := sorry
