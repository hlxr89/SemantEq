import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F 2] (p : Polynomial F) (h : p ≠ 0) (h1 : p ≠ 1) (h2 : ¬∃ (q : Polynomial F), q ≠ 0 ∧ degree q < degree p ∧ p = q * (Polynomial.X - Polynomial.C 1)): p = Polynomial.C 1 + Polynomial.X + Polynomial.C 1 := sorry
