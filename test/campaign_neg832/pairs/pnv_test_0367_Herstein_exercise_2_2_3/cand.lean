import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (h : ∀ a b : G, ∀ i : ℤ, i + 1 = i + 2 → (a * b) ^ i = a ^ i * b ^ i) : ∀ a b : G, a * b = b * a := sorry
