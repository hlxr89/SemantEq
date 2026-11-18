import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_3_1_assumed {R : Type*} [CommRing R] (a : R) :
  ∃ I : Ideal R, {x : R | x*a=0} = I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type u} [CommRing R] (a : R) : IsPrime (Ideal.span { a }) := by
  -- not proved: the statements are not equivalent; for R = ℤ and a = 4, the goal is false
  sorry
