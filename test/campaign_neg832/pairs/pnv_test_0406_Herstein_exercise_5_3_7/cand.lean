import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K] (a : K) (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
