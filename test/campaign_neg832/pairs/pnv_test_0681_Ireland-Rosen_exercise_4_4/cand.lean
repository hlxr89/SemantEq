import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} [Fact (Nat.Prime p)] (hp1 : p = 4*t + 1) : IsPrimitiveRoot (-((4*t + 1 : ℕ) : ℤ)) p ↔ IsPrimitiveRoot ((4*t + 1 : ℕ) : ℤ) p := sorry
