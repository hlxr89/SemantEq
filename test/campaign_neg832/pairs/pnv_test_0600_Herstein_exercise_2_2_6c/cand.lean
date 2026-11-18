import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type u} [Group G] (h : ∀ a b : G, ((a*b)^n = a^n * b^n)) (a b : G) : (a * b * a⁻¹ * b⁻¹)^(n*(n-1)) = 1 := sorry
