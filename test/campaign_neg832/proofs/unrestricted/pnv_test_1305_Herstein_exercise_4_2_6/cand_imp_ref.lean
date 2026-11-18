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
    a * (a * x + x * a) = (a * a) * x + (a * x) * a := by
      rw [mul_add, ← mul_assoc a a x, ← mul_assoc a x a]
    _ = (a * x) * a := by rw [← pow_two a, h, zero_mul, zero_add]
    _ = (a * x) * a + x * (a * a) := by
      rw [← pow_two a, h, mul_zero, add_zero]
    _ = (a * x + x * a) * a := by
      rw [← mul_assoc x a a, add_mul]
