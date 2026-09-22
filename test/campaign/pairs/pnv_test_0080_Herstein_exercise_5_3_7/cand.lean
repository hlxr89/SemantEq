import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {K : Type*} [Field K] {F : Subfield K} (a : K) (h : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
