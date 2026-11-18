import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {n : ℕ} (hn : 0 < n) (a b : ℕ) (h : a * b = n) (ha : Irreducible a) (hb : Irreducible b) : Irreducible n := sorry
