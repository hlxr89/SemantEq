import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {p : ℕ} [hp : Fact p.Prime] (a : ℕ) (h : a ≡ 1 [MOD p]) : a - 1 ≡ 2*(p/2) [MOD p] := sorry
