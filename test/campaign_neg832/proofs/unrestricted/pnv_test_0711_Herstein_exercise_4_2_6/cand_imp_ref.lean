import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (R : Type u) [CommRing R] (a : R) (h : a * a = 0) (x : R) : (a * x + x * a) = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_2_6 {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  have haa : a * a = 0 := by
    simpa [pow_two] using h
  calc
    a * (a * x + x * a) = (a * a) * x + (a * x) * a := by
      simp only [mul_add, ← mul_assoc]
    _ = (a * x) * a := by simp [haa]
    _ = (a * x) * a + x * (a * a) := by simp [haa]
    _ = (a * x + x * a) * a := by simp only [add_mul, mul_assoc]
