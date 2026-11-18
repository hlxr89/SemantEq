import Mathlib

open Real
open scoped BigOperators

theorem dummy {p a : ℕ} (hp : p.Prime) (h : p = 4 * a + 1) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := sorry
