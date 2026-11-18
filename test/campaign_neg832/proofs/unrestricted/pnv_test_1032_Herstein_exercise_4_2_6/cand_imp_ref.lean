import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Ring R] (a : R) (h : a^2 = 0) (x : R) : Commute a (x + x*a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_2_6 {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  have haa : a * a = 0 := by
    simpa [pow_two] using h
  rw [mul_add, add_mul, ← mul_assoc a a x, haa, zero_mul, zero_add,
    mul_assoc a x a, mul_assoc x a a, haa, mul_zero, add_zero]
