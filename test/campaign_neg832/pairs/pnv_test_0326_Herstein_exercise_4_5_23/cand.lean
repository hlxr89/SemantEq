import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [Fintype F] {p q : F[X]} (hp : Irreducible p) (hq : Irreducible q) (hf : Fintype.card F = 7) : Nonempty (RingEquiv (F[X] ⧸ Ideal.span ({p} : Set (F[X]))) (F[X] ⧸ Ideal.span ({q} : Set (F[X])))) := sorry
