import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (CommRing, Ring, IsDomain, pow,
-- neg); neither side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem sq_eq_one_domain_assumed {R} [Ring R] [IsDomain R] {x : R} (h : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_11 {R : Type*} [CommRing R] [IsDomain R]
    {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  -- a commutative domain is in particular a domain, so the candidate
  -- statement applies directly
  exact sq_eq_one_domain_assumed hx
