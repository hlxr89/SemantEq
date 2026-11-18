import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (F : Type*) [Field F] [CharP F 7] (p q : F[X]) (hp : p = X^3 - 2) (hq : q = X^3 + 2) : IsDomain F ∧ Irreducible p ∧ Irreducible q ∧ Nonempty (F[X] ⧸ Ideal.span {p} ≃+* F[X] ⧸ Ideal.span {q}) := sorry
