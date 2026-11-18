import Mathlib

open Real
open scoped BigOperators

theorem dummy {p a : ℕ} (hp : Nat.Prime p) (hpa : p ∣ a) (h4a : 4 * a + 1 = p) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := sorry
