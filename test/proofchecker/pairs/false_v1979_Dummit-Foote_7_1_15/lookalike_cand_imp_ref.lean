import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (Ring, CommRing, pow); neither
-- side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem boolean_sq_comm_assumed {R : Type*} [CommRing R] (h : ∀ (a : R), a ^ 2 = a) :
    ∀ a b : R, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) :
    ∀ a b : R, a*b = b*a := by
  -- repackage the idempotent-squaring hypothesis as a Boolean ring structure
  letI : BooleanRing R :=
    { ‹Ring R› with
      isIdempotentElem := fun a => isIdempotentElem_iff.mpr (by rw [← pow_two, hR]) }
  -- with the packaging in place the candidate statement applies verbatim
  exact boolean_sq_comm_assumed hR
