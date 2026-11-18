import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j : ℤ, j = i + 1 ∨ j = i + 2 → a * b ^ j = a ^ j * b ^ j) : Commute a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have adjacent (k : ℕ)
      (hk : (a * b) ^ k = a ^ k * b ^ k)
      (hk1 : (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    rw [pow_succ, hk, pow_succ, pow_succ] at hk1
    simp only [mul_assoc] at hk1
    apply mul_right_cancel (b := b)
    simpa only [mul_assoc] using (mul_left_cancel hk1)
  have hc0 : b ^ n * a = a * b ^ n := adjacent n (hn a b) (hn1 a b)
  have hc1 : b ^ (n + 1) * a = a * b ^ (n + 1) := adjacent (n + 1) (hn1 a b) (by simpa [Nat.add_assoc] using hn2 a b)
  rw [pow_succ] at hc1
  simp only [mul_assoc] at hc1
  have hc1' : b ^ n * (b * a) = b ^ n * (a * b) := by
    calc
      b ^ n * (b * a) = a * (b ^ n * b) := hc1
      _ = (a * b ^ n) * b := by simp only [mul_assoc]
      _ = (b ^ n * a) * b := by rw [hc0]
      _ = b ^ n * (a * b) := by simp only [mul_assoc]
  exact (mul_left_cancel hc1').symm
