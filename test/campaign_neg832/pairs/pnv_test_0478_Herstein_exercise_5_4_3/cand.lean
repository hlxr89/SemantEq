import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {p : ℚ[X]} (h : p.eval a = 0) (hp : natDegree p ≤ 80) : IsAlgebraic ℚ a := sorry
