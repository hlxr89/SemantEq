import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {K F : Type*} [Field K] [Field F] [Algebra F K] {a : K} (ha2 : IsAlgebraic (F) (a^2)) : IsAlgebraic (F) a := sorry
