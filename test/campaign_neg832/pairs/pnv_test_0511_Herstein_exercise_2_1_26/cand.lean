import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] [DecidableEq G] {p z : ℕ} (hp : Nat.Prime p) (hz : Fintype.card G = p ^ z) (n : ℕ) [hzp : Fact (z ≤ p)] : ∃ m : ℕ, 0 < m ∧ a ^ m = 1 := sorry
