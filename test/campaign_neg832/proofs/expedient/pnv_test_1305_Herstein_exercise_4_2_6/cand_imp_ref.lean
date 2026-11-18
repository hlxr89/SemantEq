import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommSemiring R] {a x : R} (h : a^2 = 0) : Commute a (x + x * a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_2_6 {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  calc
    a * (a * x + x * a) = (a ^ 2) * x + (a * x) * a := by noncomm_ring
    _ = (a * x) * a := by simp [h]
    _ = (a * x) * a + x * (a ^ 2) := by simp [h]
    _ = (a * x + x * a) * a := by noncomm_ring
