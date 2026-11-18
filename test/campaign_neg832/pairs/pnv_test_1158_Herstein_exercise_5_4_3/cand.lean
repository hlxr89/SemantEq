import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (p : Polynomial ℚ) (h0 : p ≠ 0) (h : p.natDegree = 5) (ha : a ∈ roots p) : ∃ q ∈ {q : Polynomial ℚ | Irreducible q ∧ q.natDegree ≤ 80}, q ∣ p := sorry
