import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have hc (k : ℕ) (hk : (a * b) ^ k = a ^ k * b ^ k)
      (hk1 : (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    apply mul_left_cancel (a := a ^ k)
    apply mul_right_cancel (b := b)
    calc
      a ^ k * (b ^ k * a) * b = (a ^ k * b ^ k) * (a * b) := by simp only [mul_assoc]
      _ = (a * b) ^ k * (a * b) := by rw [hk]
      _ = (a * b) ^ (k + 1) := by rw [pow_succ]
      _ = a ^ (k + 1) * b ^ (k + 1) := hk1
      _ = a ^ k * (a * b ^ k) * b := by simp only [pow_succ, mul_assoc]
  have hcn : b ^ n * a = a * b ^ n := hc n (hn a b) (hn1 a b)
  have hcn1 : b ^ (n + 1) * a = a * b ^ (n + 1) := hc (n + 1) (hn1 a b) (by simpa [Nat.add_assoc] using hn2 a b)
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = a * (b ^ n * b) := by rw [← mul_assoc, hcn, mul_assoc]
    _ = (b ^ n * b) * a := by simpa only [pow_succ] using hcn1.symm
    _ = b ^ n * (b * a) := by rw [mul_assoc]
