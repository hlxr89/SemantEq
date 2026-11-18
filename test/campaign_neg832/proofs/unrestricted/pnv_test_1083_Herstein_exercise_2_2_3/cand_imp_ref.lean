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
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have e1 : b ^ n * a = a * b ^ n := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ n)
    simpa only [pow_succ, hn a b, mul_assoc] using hn1 a b
  have e2 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ (n + 1))
    simpa only [pow_succ, hn1 a b, mul_assoc] using hn2 a b
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (b ^ n * a) * b := by rw [mul_assoc]
    _ = (a * b ^ n) * b := by rw [e1]
    _ = a * b ^ (n + 1) := by rw [pow_succ, mul_assoc]
    _ = b ^ (n + 1) * a := e2.symm
    _ = b ^ n * (b * a) := by rw [pow_succ, mul_assoc]
