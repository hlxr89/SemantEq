import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {K L : Type*} [Field K] [Field L] [Algebra K L] {a : L} (h : IsAlgebraic K (a^2)) : IsAlgebraic K a := sorry
