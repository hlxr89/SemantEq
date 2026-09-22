import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i + 1) = a ^ (i + 1) * b ^ (i + 1) ∧ (a * b) ^ (i + 2) = a ^ (i + 2) * b ^ (i + 2)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  rw [hP] at hP1
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have h0 := hn a b
  have h1 := hn1 a b
  have h2 := hn2 a b
  have hpow_n : b ^ n * a = a * b ^ n := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ n)
    simpa only [pow_succ, h0, mul_assoc] using h1
  have h2' :
      (a * b) ^ ((n + 1) + 1) =
        a ^ ((n + 1) + 1) * b ^ ((n + 1) + 1) := by
    simpa [add_assoc] using h2
  have hpow_n1 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ (n + 1))
    simpa only [pow_succ, h1, mul_assoc] using h2'
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (b ^ n * a) * b := by rw [mul_assoc]
    _ = (a * b ^ n) * b := by rw [hpow_n]
    _ = a * (b ^ n * b) := by rw [mul_assoc]
    _ = a * b ^ (n + 1) := by rw [pow_succ]
    _ = b ^ (n + 1) * a := hpow_n1.symm
    _ = (b ^ n * b) * a := by rw [pow_succ]
    _ = b ^ n * (b * a) := by rw [mul_assoc]
