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
  have ha : a * a = 0 := by simpa [pow_two] using h
  rw [mul_add, add_mul, ← mul_assoc a a x, mul_assoc x a a, ha]
  simp [mul_assoc]
