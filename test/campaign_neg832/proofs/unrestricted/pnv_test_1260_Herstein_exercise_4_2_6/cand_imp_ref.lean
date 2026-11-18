import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] (a : R) (h : a ^ 2 = 0) : ∀ x : R, a * x + x * a = a * (a * x + x * a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_2_6 {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  have haa : a * a = 0 := by
    simpa [pow_two] using h
  calc
    a * (a * x + x * a) = (a * a) * x + (a * x) * a := by
      rw [mul_add, ← mul_assoc, ← mul_assoc]
    _ = (a * x) * a := by simp [haa]
    _ = (a * x) * a + x * (a * a) := by simp [haa]
    _ = (a * x + x * a) * a := by rw [add_mul, mul_assoc x a a]
