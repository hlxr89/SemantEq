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
  let w : Fin n → ℝ := fun i => (i : ℝ) + 1
  let x : Fin (n + 1) → ℝ := Fin.cons 0 (fun i => Real.sqrt (w i) * a i)
  let y : Fin (n + 1) → ℝ := Fin.cons 0 (fun i => b i / Real.sqrt (w i))
  have hw (i : Fin n) : 0 < w i := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg i) zero_lt_one
  have hsquare (i : Fin n) : (Real.sqrt (w i)) ^ 2 = w i := by
    exact Real.sq_sqrt (le_of_lt (hw i))
  have hsqrt (i : Fin n) : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw i))
  have hcast (i : Fin n) : ((i.succ : Fin (n + 1)) : ℝ) = w i := by
    simp [w]
  have hxy (i : Fin n) : x i.succ * y i.succ = a i * b i := by
    simp only [x, y, Fin.cons_succ]
    field_simp [hsqrt i]
  have hxa (i : Fin n) :
      (i.succ : ℝ) * x i.succ ^ 2 * (1 / (i.succ : ℝ)) = w i * a i ^ 2 := by
    rw [hcast]
    field_simp [ne_of_gt (hw i)]
    simp only [x, Fin.cons_succ]
    rw [mul_pow, hsquare]
  have hyb (i : Fin n) :
      (i.succ : ℝ) * y i.succ ^ 2 / (i.succ : ℝ) = b i ^ 2 / w i := by
    rw [hcast]
    field_simp [ne_of_gt (hw i), hsqrt i]
    simp only [y, Fin.cons_succ]
    field_simp [hsqrt i]
    rw [hsquare]
    ring
  have hdot : (∑ i, x i * y i) = ∑ i, a i * b i := by
    rw [Fin.sum_univ_succ]
    rw [show x 0 * y 0 = 0 by simp [x, y], zero_add]
    exact Finset.sum_congr rfl fun i _ => hxy i
  have hsumx :
      (∑ i : Fin (n + 1), (i : ℝ) * x i ^ 2 * (1 / (i : ℝ))) =
        ∑ i, w i * a i ^ 2 := by
    rw [Fin.sum_univ_succ]
    rw [show ((0 : Fin (n + 1)) : ℝ) * x 0 ^ 2 *
      (1 / ((0 : Fin (n + 1)) : ℝ)) = 0 by norm_num, zero_add]
    exact Finset.sum_congr rfl fun i _ => hxa i
  have hsumy :
      (∑ i : Fin (n + 1), (i : ℝ) * y i ^ 2 / (i : ℝ)) =
        ∑ i, b i ^ 2 / w i := by
    rw [Fin.sum_univ_succ]
    rw [show ((0 : Fin (n + 1)) : ℝ) * y 0 ^ 2 /
      ((0 : Fin (n + 1)) : ℝ) = 0 by norm_num, zero_add]
    exact Finset.sum_congr rfl fun i _ => hyb i
  have h := dummy_assumed x y
  rw [hdot, ← Finset.sum_mul, hsumx, hsumy] at h
  simpa [w] using h
