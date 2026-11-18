import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {n : ℕ} (hn : 2 < n) (h : ∀ a b : G, a * b * a⁻¹ * b⁻¹ = (a * b) ^ n → a * b = a * b) : ∀ a b : G, a * b * a⁻¹ * b⁻¹ = (a * b) ^ (n*(n-1)) := sorry
