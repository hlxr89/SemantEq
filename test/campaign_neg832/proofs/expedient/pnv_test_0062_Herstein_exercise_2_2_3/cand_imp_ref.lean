import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i * b ^ i) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  rw [hP] at hn hn1 hn2
  intro a b
  have e1 : b ^ n * a = a * b ^ n := by
    apply mul_left_cancel (a := a ^ n)
    apply mul_right_cancel (b := b)
    have e : a ^ (n + 1) * b ^ (n + 1) = a ^ n * b ^ n * (a * b) := by
      calc
        a ^ (n + 1) * b ^ (n + 1) = (a * b) ^ (n + 1) := (hn1 a b).symm
        _ = (a * b) ^ n * (a * b) := by rw [pow_succ]
        _ = a ^ n * b ^ n * (a * b) := by rw [hn a b]
    simpa [pow_succ, mul_assoc] using e.symm
  have e2 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_left_cancel (a := a ^ (n + 1))
    apply mul_right_cancel (b := b)
    have e : a ^ (n + 2) * b ^ (n + 2) = a ^ (n + 1) * b ^ (n + 1) * (a * b) := by
      calc
        a ^ (n + 2) * b ^ (n + 2) = (a * b) ^ (n + 2) := (hn2 a b).symm
        _ = (a * b) ^ (n + 1) * (a * b) := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        _ = a ^ (n + 1) * b ^ (n + 1) * (a * b) := by rw [hn1 a b]
    simpa [show n + 2 = (n + 1) + 1 by omega, pow_succ, mul_assoc] using e.symm
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (b ^ n * a) * b := by simp [mul_assoc]
    _ = (a * b ^ n) * b := by rw [e1]
    _ = a * b ^ (n + 1) := by rw [pow_succ, mul_assoc]
    _ = b ^ (n + 1) * a := e2.symm
    _ = b ^ n * (b * a) := by rw [pow_succ, mul_assoc]
