import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {p : ℕ} (h₁ : Fact p.Prime) (h₂ : p % 2 = 1) : (Finset.range (p - 1)).filter (fun i : ℕ => i^2 ≡ 1 [MOD p]) = Finset.filter (fun i : ℕ => i % 2 = 0) (Finset.range (p - 1)) := sorry
