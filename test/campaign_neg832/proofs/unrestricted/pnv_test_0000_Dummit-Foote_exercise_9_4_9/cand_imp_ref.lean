import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (F : Type*) [Field F] {p : F[X]} (h_no_roots : ∀ a, p.eval a ≠ 0) : Irreducible p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have h_one : Irreducible (1 : (ℚ)[X]) :=
    dummy_assumed ℚ (p := 1) (by simp)
  exact (h_one.not_isUnit isUnit_one).elim
