import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := sorry
