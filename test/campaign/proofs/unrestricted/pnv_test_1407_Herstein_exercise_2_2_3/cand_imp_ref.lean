import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i+1) = a ^ (i+1) * b ^ (i+1) ∧ (a * b) ^ (i+2) = a ^ (i+2) * b ^ (i+2)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  obtain ⟨n, hn0, hn1, hn2⟩ := hP1
  rw [hP] at hn0 hn1 hn2
  intro a b
  have hc0 : b ^ n * a = a * b ^ n := by
    apply mul_left_cancel (a := a ^ n)
    apply mul_right_cancel (b := b)
    calc
      a ^ n * (b ^ n * a) * b = (a * b) ^ n * (a * b) := by
        rw [hn0 a b]
        simp only [mul_assoc]
      _ = (a * b) ^ (n + 1) := (pow_succ (a * b) n).symm
      _ = a ^ (n + 1) * b ^ (n + 1) := hn1 a b
      _ = a ^ n * (a * b ^ n) * b := by
        rw [pow_succ a n, pow_succ b n]
        simp only [mul_assoc]
  have hc1 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_left_cancel (a := a ^ (n + 1))
    apply mul_right_cancel (b := b)
    calc
      a ^ (n + 1) * (b ^ (n + 1) * a) * b = (a * b) ^ (n + 1) * (a * b) := by
        rw [hn1 a b]
        simp only [mul_assoc]
      _ = (a * b) ^ ((n + 1) + 1) := (pow_succ (a * b) (n + 1)).symm
      _ = (a * b) ^ (n + 2) := by congr 1 <;> omega
      _ = a ^ (n + 2) * b ^ (n + 2) := hn2 a b
      _ = a ^ ((n + 1) + 1) * b ^ ((n + 1) + 1) := by congr 2 <;> omega
      _ = a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
        rw [pow_succ a (n + 1), pow_succ b (n + 1)]
        simp only [mul_assoc]
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (b ^ n * a) * b := by simp only [mul_assoc]
    _ = a * b ^ n * b := by rw [hc0]
    _ = a * b ^ (n + 1) := by rw [pow_succ b n]; simp only [mul_assoc]
    _ = b ^ (n + 1) * a := hc1.symm
    _ = b ^ n * (b * a) := by rw [pow_succ b n]; simp only [mul_assoc]
