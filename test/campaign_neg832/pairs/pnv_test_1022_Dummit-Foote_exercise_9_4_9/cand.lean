import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [EuclideanDomain R] [IsDomain R] (h : (2 : R) ≠ 0) : Irreducible (X^2 - 2*X + 2 : R[X]) := sorry
