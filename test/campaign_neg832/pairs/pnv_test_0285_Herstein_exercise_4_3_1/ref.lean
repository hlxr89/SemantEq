import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem exercise_4_3_1 {R : Type*} [CommRing R] (a : R) :
  ∃ I : Ideal R, {x : R | x*a=0} = I := sorry
