import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : ℤ[X]) (hp1 : p.degree = 4) (hp2 : p.eval (-1) = 1) (hp3 : p.eval 1 = 1) : Irreducible p := sorry
