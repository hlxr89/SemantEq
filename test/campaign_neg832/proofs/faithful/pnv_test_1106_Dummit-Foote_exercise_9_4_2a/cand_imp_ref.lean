import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (f : R[X]) (h : f = X^4 - 4 * X^3 + 6) : ¬ ∃ (g : R[X]) (h : R[X]), f = g * (X - 1) * (X - 2) * (X - 3) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  -- not proved: excluding one fixed three-linear-factor divisor is strictly weaker than irreducibility and supplies no transport proof
  sorry
