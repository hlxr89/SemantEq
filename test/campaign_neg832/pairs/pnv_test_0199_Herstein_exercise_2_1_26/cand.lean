import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact (Nat.Prime p)] (hG : Fintype.card G = p ^ n) {k : ℕ} (hk : n < k) : ∃ (m : ℕ), 0 < m ∧ a ^ m = 1 := sorry
