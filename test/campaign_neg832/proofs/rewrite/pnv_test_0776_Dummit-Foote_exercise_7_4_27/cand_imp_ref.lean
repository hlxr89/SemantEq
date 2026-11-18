import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] {a b : R} (ha : IsNilpotent a) (hb : b ≠ 0) : IsUnit (1 - a * b) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b) := by
  have hab : IsNilpotent (a * b) := by
    rcases ha with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [mul_pow, hn, zero_mul]
  have hu := dummy_assumed (a := a * b) (b := 1) hab (Ne.symm hR)
  simpa only [mul_one] using hu
