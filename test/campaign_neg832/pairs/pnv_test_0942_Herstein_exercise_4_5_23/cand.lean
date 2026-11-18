import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type u} [Field F] (p q : F[X]) (hp : Irreducible p) (hq : Irreducible q) : IsField (F[X] ⧸ Ideal.span {p}) ∧ IsField (F[X] ⧸ Ideal.span {q}) ∧ Nonempty (F[X] ⧸ Ideal.span {p} ≃+* F[X] ⧸ Ideal.span {q}) := sorry
