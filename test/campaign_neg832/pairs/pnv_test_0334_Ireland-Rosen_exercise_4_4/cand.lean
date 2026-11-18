import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : p.Prime) (h : ∃ t, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := sorry
