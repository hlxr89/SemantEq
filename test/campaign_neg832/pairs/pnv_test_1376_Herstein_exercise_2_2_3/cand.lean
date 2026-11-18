import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (a b : G) (m n : ℤ) (h : ∀ (x : ℤ), m < x → x < n → a * b ^ x = a ^ x * b ^ x) : ∀ (x y : G), x * y = y * x := sorry
