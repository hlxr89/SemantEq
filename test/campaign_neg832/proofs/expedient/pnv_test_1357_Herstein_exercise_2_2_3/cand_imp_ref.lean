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
  have hs1 : (a * b) ^ n * (a * b) = (a ^ n * a) * (b ^ n * b) := by
    simpa only [pow_succ] using hn1 a b
  rw [hn a b] at hs1
  have hc1 : b ^ n * a = a * b ^ n := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ n)
    simpa only [mul_assoc] using hs1
  have hs2 : (a * b) ^ (n + 1) * (a * b) = (a ^ (n + 1) * a) * (b ^ (n + 1) * b) := by
    simpa only [pow_succ, Nat.add_assoc] using hn2 a b
  rw [hn1 a b] at hs2
  have hc2 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ (n + 1))
    simpa only [mul_assoc] using hs2
  symm
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (b * a) = b ^ (n + 1) * a := by rw [pow_succ, mul_assoc]
    _ = a * b ^ (n + 1) := hc2
    _ = (a * b ^ n) * b := by rw [pow_succ, mul_assoc]
    _ = (b ^ n * a) * b := by rw [hc1]
    _ = b ^ n * (a * b) := by rw [mul_assoc]
