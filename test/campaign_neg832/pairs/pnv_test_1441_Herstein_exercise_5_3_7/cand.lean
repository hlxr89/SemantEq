import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F K : Type*} [Field F] [Field K] [Algebra F K] {a : K} (h : IsAlgebraic F (a^2)) : IsAlgebraic F a := sorry
