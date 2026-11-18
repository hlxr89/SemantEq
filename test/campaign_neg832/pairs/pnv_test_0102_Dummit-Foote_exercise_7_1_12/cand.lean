import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {K : Type*} [Field K] {S : Type*} [Ring S] [Algebra K S] (h : ∃ (k : K), algebraMap K S k = 1) : NoZeroDivisors S := sorry
