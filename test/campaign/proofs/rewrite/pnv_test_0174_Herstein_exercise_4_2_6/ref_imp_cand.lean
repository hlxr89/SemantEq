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
theorem dummy {R : Type*} [Ring R] (ha : a ^ 2 = 0) : ∀ x : R, Commute (a * x + x * a) a := by
  intro x
  have haR : (a : R) ^ 2 = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_zero] using
      congrArg (fun n : ℕ ↦ (n : R)) ha
  exact (exercise_4_2_6_assumed (a : R) x haR).symm
