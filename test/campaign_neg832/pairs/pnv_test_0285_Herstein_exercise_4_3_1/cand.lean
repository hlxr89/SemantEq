import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type u} [CommRing R] (a : R) : IsPrime (Ideal.span { a }) := sorry
