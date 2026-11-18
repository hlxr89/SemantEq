import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (h : n ≠ 0) {a b : Fin n → ℝ} : (∑ i, a i * b i) ^ 2 ≤ (∑ i, i * a i ^ 2) * ∑ i, b i ^ 2 / i := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_6_3 {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : Fin n, (i + 1) * a i ^ 2) * (∑ i, b i ^ 2 / (i + 1)) := by
  have h := dummy_assumed (n := n + 1) (Nat.succ_ne_zero n)
    (a := Fin.cases 0 a) (b := Fin.cases 0 b)
  simpa [Fin.sum_univ_succ] using h
