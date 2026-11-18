import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i * b ^ i) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have e0 := hn a b
  have e1 := hn1 a b
  have e2 := hn2 a b
  have c0 : b ^ n * a = a * b ^ n := by
    apply mul_left_cancel (a := a ^ n)
    apply mul_right_cancel (b := b)
    calc
      (a ^ n * (b ^ n * a)) * b = (a ^ n * b ^ n) * (a * b) := by simp [mul_assoc]
      _ = (a * b) ^ n * (a * b) := by rw [e0]
      _ = (a * b) ^ (n + 1) := by rw [pow_succ]
      _ = a ^ (n + 1) * b ^ (n + 1) := e1
      _ = (a ^ n * (a * b ^ n)) * b := by simp [pow_succ, mul_assoc]
  have c1 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_left_cancel (a := a ^ (n + 1))
    apply mul_right_cancel (b := b)
    calc
      (a ^ (n + 1) * (b ^ (n + 1) * a)) * b =
          (a ^ (n + 1) * b ^ (n + 1)) * (a * b) := by simp [mul_assoc]
      _ = (a * b) ^ (n + 1) * (a * b) := by rw [e1]
      _ = (a * b) ^ (n + 2) := by
        rw [show n + 2 = (n + 1) + 1 by omega]
        exact (pow_succ (a * b) (n + 1)).symm
      _ = a ^ (n + 2) * b ^ (n + 2) := e2
      _ = (a ^ (n + 1) * (a * b ^ (n + 1))) * b := by
        rw [show n + 2 = (n + 1) + 1 by omega]
        simp [pow_succ, mul_assoc]
  have hcancel : b ^ n * (b * a) = b ^ n * (a * b) := by
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by simp [pow_succ, mul_assoc]
      _ = a * b ^ (n + 1) := c1
      _ = (a * b ^ n) * b := by simp [pow_succ, mul_assoc]
      _ = (b ^ n * a) * b := by rw [c0]
      _ = b ^ n * (a * b) := by simp [mul_assoc]
  exact (mul_left_cancel hcancel).symm
