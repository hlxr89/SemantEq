import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (Ring, CommRing, pow); neither
-- side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_7_1_15_assumed {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) :
    ∀ a b : R, a*b = b*a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem boolean_sq_comm_cand {R : Type*} [CommRing R] (h : ∀ (a : R), a ^ 2 = a) :
    ∀ a b : R, a * b = b * a := by
  -- the reference statement covers every ring with idempotent squaring, in
  -- particular the present one
  intro a b
  exact exercise_7_1_15_assumed h a b
