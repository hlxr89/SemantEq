import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∀ a b : G, ∀ i j k : ℤ, (a * b) ^ i * (a * b) ^ j = (a ^ i) * (b ^ i) * (a ^ j) * (b ^ j)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  intro a b
  have e1 := hn a b
  have e2 := hn1 a b
  have e3 := hn2 a b
  have hc1 : b ^ n * a = a * b ^ n := by
    apply mul_left_cancel (a := a ^ n)
    apply mul_right_cancel (b := b)
    calc
      a ^ n * (b ^ n * a) * b = (a ^ n * b ^ n) * (a * b) := by simp [mul_assoc]
      _ = (a * b) ^ n * (a * b) := by rw [e1]
      _ = (a * b) ^ (n + 1) := by rw [pow_succ]
      _ = a ^ (n + 1) * b ^ (n + 1) := e2
      _ = a ^ n * (a * b ^ n) * b := by simp [pow_succ, mul_assoc]
  have hc2 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_left_cancel (a := a ^ (n + 1))
    apply mul_right_cancel (b := b)
    calc
      a ^ (n + 1) * (b ^ (n + 1) * a) * b = (a ^ (n + 1) * b ^ (n + 1)) * (a * b) := by simp [mul_assoc]
      _ = (a * b) ^ (n + 1) * (a * b) := by rw [e2]
      _ = (a * b) ^ (n + 2) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        simp [pow_succ, mul_assoc]
      _ = a ^ (n + 2) * b ^ (n + 2) := e3
      _ = a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
        rw [show n + 2 = (n + 1) + 1 by omega]
        simp [pow_succ, mul_assoc]
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (a * b ^ n) * b := by rw [← hc1]; simp [mul_assoc]
    _ = a * b ^ (n + 1) := by simp [pow_succ, mul_assoc]
    _ = b ^ (n + 1) * a := hc2.symm
    _ = b ^ n * (b * a) := by simp [pow_succ, mul_assoc]
