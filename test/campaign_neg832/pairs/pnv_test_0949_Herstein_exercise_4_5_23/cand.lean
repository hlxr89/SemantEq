import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] (p q : F[X]) (hp : Irreducible p) (hq : Irreducible q) (h : p %ₘ q = 0 → q %ₘ p = 0) : Irreducible (p * q) := sorry
