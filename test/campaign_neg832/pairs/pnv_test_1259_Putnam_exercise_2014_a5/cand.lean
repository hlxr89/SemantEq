import Mathlib

open scoped BigOperators

theorem dummy {p : ℕ} (hp : 2 < p) (hpr : p.Prime) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hab2 : a < b ^ 2) : ∃ (x y z w : ℕ), p = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 := sorry
