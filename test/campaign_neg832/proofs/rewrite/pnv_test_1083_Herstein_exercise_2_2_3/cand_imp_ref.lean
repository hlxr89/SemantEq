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
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  rw [hP] at hn hn1 hn2
  have hcomm : ∀ a b : G, Commute a b := by
    intro a b
    have en : b ^ n * a = a * b ^ n := by
      have e : a ^ n * (b ^ n * a) * b = a ^ n * (a * b ^ n) * b := by
        have e' := hn1 a b
        rw [pow_succ, hn a b, pow_succ, pow_succ] at e'
        simpa only [mul_assoc] using e'
      exact mul_left_cancel (mul_right_cancel e)
    have en1 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
      have e : a ^ (n + 1) * (b ^ (n + 1) * a) * b =
          a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
        have e' := hn2 a b
        change (a * b) ^ ((n + 1) + 1) =
          a ^ ((n + 1) + 1) * b ^ ((n + 1) + 1) at e'
        rw [pow_succ (a * b) (n + 1), hn1 a b,
          pow_succ a (n + 1), pow_succ b (n + 1)] at e'
        simpa only [mul_assoc] using e'
      exact mul_left_cancel (mul_right_cancel e)
    apply Commute.symm
    show b * a = a * b
    apply mul_left_cancel (a := b ^ n)
    rw [← mul_assoc, ← pow_succ, en1, pow_succ, ← mul_assoc, ← en, mul_assoc]
  apply dummy_assumed
  intro a b i j k
  rw [(hcomm a b).mul_zpow i, (hcomm a b).mul_zpow j]
  simp only [mul_assoc]
