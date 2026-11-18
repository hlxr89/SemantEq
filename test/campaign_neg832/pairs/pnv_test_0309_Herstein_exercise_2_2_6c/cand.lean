import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {n : ℕ} (hn : 1 < n) (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) (a b : G) (hab : (a * b) ^ n = 1) : (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := sorry
