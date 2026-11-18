import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (a b : Fin n → ℝ) : (∑ i, a i * b i)^2 ≤ ∑ i, i * a i^2 * (1/(i : ℝ)) * ∑ j, j * b j^2 / (j : ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_6_3 {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : Fin n, (i + 1) * a i ^ 2) * (∑ i, b i ^ 2 / (i + 1)) := by
  let A : Fin (n + 1) → ℝ := Fin.cases 0 (fun i => Real.sqrt ((i : ℝ) + 1) * a i)
  let B : Fin (n + 1) → ℝ := Fin.cases 0 (fun i => b i / Real.sqrt ((i : ℝ) + 1))
  have hdot : (∑ i, A i * B i) = ∑ i, a i * b i := by
    rw [Fin.sum_univ_succ]
    simp only [A, B, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Fin.cases_succ]
    have hp : 0 < (i : ℝ) + 1 := by positivity
    have hs : Real.sqrt ((i : ℝ) + 1) ≠ 0 := Real.sqrt_ne_zero'.mpr hp
    rw [div_eq_mul_inv, mul_assoc,
      mul_comm (b i) (Real.sqrt ((i : ℝ) + 1))⁻¹,
      ← mul_assoc (a i) (Real.sqrt ((i : ℝ) + 1))⁻¹ (b i),
      ← mul_assoc (Real.sqrt ((i : ℝ) + 1))
        (a i * (Real.sqrt ((i : ℝ) + 1))⁻¹) (b i),
      ← mul_assoc (Real.sqrt ((i : ℝ) + 1)) (a i)
        (Real.sqrt ((i : ℝ) + 1))⁻¹,
      mul_comm (Real.sqrt ((i : ℝ) + 1)) (a i),
      mul_assoc (a i) (Real.sqrt ((i : ℝ) + 1))
        (Real.sqrt ((i : ℝ) + 1))⁻¹,
      mul_inv_cancel₀ hs, mul_one]
  have hfirst :
      (∑ i : Fin (n + 1), (i : ℝ) * A i ^ 2 * (1 / (i : ℝ))) =
        ∑ i : Fin n, (i + 1) * a i ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp only [A, Fin.cases_zero, Fin.cases_succ, Fin.val_succ, Nat.cast_add,
      Nat.cast_one, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hx : 0 ≤ (i : ℝ) + 1 := by positivity
    have hn : (i : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    rw [mul_pow, Real.sq_sqrt hx, one_div,
      mul_comm ((i : ℝ) + 1) (((i : ℝ) + 1) * a i ^ 2),
      mul_assoc (((i : ℝ) + 1) * a i ^ 2) ((i : ℝ) + 1) (((i : ℝ) + 1)⁻¹),
      mul_inv_cancel₀ hn, mul_one]
  have hsecond :
      (∑ i : Fin (n + 1), (i : ℝ) * B i ^ 2 / (i : ℝ)) =
        ∑ i : Fin n, b i ^ 2 / (i + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [B, Fin.cases_zero, Fin.cases_succ, Fin.val_succ, Nat.cast_add,
      Nat.cast_one, Fin.val_zero, Nat.cast_zero, zero_mul, zero_div, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hx : 0 ≤ (i : ℝ) + 1 := by positivity
    have hn : (i : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    rw [mul_div_cancel_left₀ _ hn, div_pow, Real.sq_sqrt hx]
  have h := dummy_assumed A B
  rw [← Finset.sum_mul, hdot, hfirst, hsecond] at h
  exact h
