import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (F : Type*) [Field F] {p : F[X]} (h_no_roots : ∀ a, p.eval a ≠ 0) : Irreducible p := sorry
