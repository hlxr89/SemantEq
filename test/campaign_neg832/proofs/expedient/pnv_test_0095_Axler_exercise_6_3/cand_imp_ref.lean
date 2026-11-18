import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (a b : Fin n → ℝ) : (∑ j, a j * b j) ^ 2 ≤ (∑ j, j * (a j) ^ 2) * (∑ j, (b j) ^ 2 / j) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_6_3 {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : Fin n, (i + 1) * a i ^ 2) * (∑ i, b i ^ 2 / (i + 1)) := by
  have hw (i : Fin n) : 0 < (i : ℝ) + 1 := by positivity
  have hs (i : Fin n) : Real.sqrt ((i : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (hw i))
  calc
    (∑ i, a i * b i) ^ 2 =
        (∑ i : Fin n, (Real.sqrt ((i : ℝ) + 1) * a i) *
          (b i / Real.sqrt ((i : ℝ) + 1))) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hs i]
    _ ≤ (∑ i : Fin n, (Real.sqrt ((i : ℝ) + 1) * a i) ^ 2) *
          (∑ i : Fin n, (b i / Real.sqrt ((i : ℝ) + 1)) ^ 2) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin n => Real.sqrt ((i : ℝ) + 1) * a i)
        (fun i : Fin n => b i / Real.sqrt ((i : ℝ) + 1))
    _ = (∑ i : Fin n, (i + 1) * a i ^ 2) * (∑ i, b i ^ 2 / (i + 1)) := by
      apply congrArg₂ (· * ·)
      · apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow, Real.sq_sqrt (le_of_lt (hw i))]
      · apply Finset.sum_congr rfl
        intro i _
        rw [div_pow, Real.sq_sqrt (le_of_lt (hw i))]
