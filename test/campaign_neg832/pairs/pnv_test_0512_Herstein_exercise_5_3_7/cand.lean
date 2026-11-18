import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (K : Type*) [Field K] (F : Subfield K) (a : K) (ha : a ^ 2 ∈ F) : a ∈ F := sorry
