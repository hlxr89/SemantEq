import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (a b : G) (ha : a ^ 2 = a) (hb : b ^ 2 = b) (hc : a ^ 3 * b ^ 3 = a ^ 3 * b): a = b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  intro a b
  have hcomm_n : b ^ n * a = a * b ^ n := by
    have h : a ^ n * (b ^ n * a) * b = a ^ n * (a * b ^ n) * b := by calc
      a ^ n * (b ^ n * a) * b = (a ^ n * b ^ n) * (a * b) := by simp [mul_assoc]
      _ = (a * b) ^ n * (a * b) := by rw [hn a b]
      _ = (a * b) ^ (n + 1) := by rw [pow_succ]
      _ = a ^ (n + 1) * b ^ (n + 1) := hn1 a b
      _ = a ^ n * (a * b ^ n) * b := by simp [pow_succ, mul_assoc]
    exact mul_left_cancel (mul_right_cancel h)
  have hcomm_n1 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    have h : a ^ (n + 1) * (b ^ (n + 1) * a) * b =
        a ^ (n + 1) * (a * b ^ (n + 1)) * b := by calc
      a ^ (n + 1) * (b ^ (n + 1) * a) * b =
          (a ^ (n + 1) * b ^ (n + 1)) * (a * b) := by simp only [mul_assoc]
      _ = (a * b) ^ (n + 1) * (a * b) := by rw [hn1 a b]
      _ = (a * b) ^ (n + 2) := by
        convert (pow_succ (a * b) (n + 1)).symm using 1 <;> omega
      _ = a ^ (n + 2) * b ^ (n + 2) := hn2 a b
      _ = a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
        have ha : a ^ (n + 2) = a ^ (n + 1) * a := by
          convert pow_succ a (n + 1) using 1 <;> omega
        have hb : b ^ (n + 2) = b ^ (n + 1) * b := by
          convert pow_succ b (n + 1) using 1 <;> omega
        rw [ha, hb]
        simp only [mul_assoc]
    exact mul_left_cancel (mul_right_cancel h)
  have hfinal : b ^ n * (a * b) = b ^ n * (b * a) := by calc
    b ^ n * (a * b) = (b ^ n * a) * b := by simp only [mul_assoc]
    _ = (a * b ^ n) * b := by rw [hcomm_n]
    _ = a * (b ^ n * b) := by simp only [mul_assoc]
    _ = a * b ^ (n + 1) := by rw [pow_succ]
    _ = b ^ (n + 1) * a := hcomm_n1.symm
    _ = (b ^ n * b) * a := by rw [pow_succ]
    _ = b ^ n * (b * a) := by simp only [mul_assoc]
  exact mul_left_cancel hfinal
