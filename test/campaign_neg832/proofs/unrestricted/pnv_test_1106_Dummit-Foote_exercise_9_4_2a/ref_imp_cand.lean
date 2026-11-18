import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2a_assumed : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (f : R[X]) (h : f = X^4 - 4 * X^3 + 6) : ¬ ∃ (g : R[X]) (h : R[X]), f = g * (X - 1) * (X - 2) * (X - 3) := by
  rintro ⟨g, q, hfac⟩
  have heval := congrArg (Polynomial.eval (1 : R)) hfac
  rw [h] at heval
  norm_num at heval
