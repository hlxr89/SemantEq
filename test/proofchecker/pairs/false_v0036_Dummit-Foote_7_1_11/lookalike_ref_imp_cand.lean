import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (CommRing, Ring, IsDomain, pow,
-- neg); neither side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_7_1_11_assumed {R : Type*} [CommRing R] [IsDomain R]
    {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem sq_eq_one_domain_cand {R} [Ring R] [IsDomain R] {x : R} (h : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  -- consult the reference classification over the initial domain ℤ to orient
  -- the two root branches
  rcases exercise_7_1_11_assumed (R := ℤ) (x := -1) (by norm_num) with horient | horient
  · norm_num at horient
  · -- fold the square and read the roots off the self-multiplication form
    rw [← mul_self_eq_one_iff, ← pow_two]
    exact h
