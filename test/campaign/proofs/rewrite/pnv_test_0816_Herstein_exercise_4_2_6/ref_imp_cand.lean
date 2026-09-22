import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_2_6_assumed {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (R : Type*) [Ring R] (a x : R) (h : a^2 = 0) : Commute (x * a + a * x) a := by
  rw [add_comm (x * a) (a * x)]
  exact (exercise_4_2_6_assumed a x h).symm
