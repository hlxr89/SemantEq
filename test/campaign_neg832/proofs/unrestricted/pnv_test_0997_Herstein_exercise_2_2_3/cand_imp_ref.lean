import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ i = a^i * b^i) (i : ℕ) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  rw [hP] at hn hn1 hn2
  intro a b
  have e1 := hn1 a b
  rw [pow_succ, pow_succ, pow_succ, hn a b] at e1
  have c1 : b ^ n * a = a * b ^ n := by
    simpa [mul_assoc] using
      congrArg (fun x : G => (a ^ n)⁻¹ * x * b⁻¹) e1
  have e2 : (a ^ (n + 1) * b ^ (n + 1)) * (a * b) =
      (a ^ (n + 1) * a) * (b ^ (n + 1) * b) := by
    calc
      (a ^ (n + 1) * b ^ (n + 1)) * (a * b) =
          (a * b) ^ (n + 1) * (a * b) := by rw [hn1 a b]
      _ = (a * b) ^ (n + 2) := by
        rw [show n + 2 = (n + 1) + 1 by omega]
        exact (pow_succ (a * b) (n + 1)).symm
      _ = a ^ (n + 2) * b ^ (n + 2) := hn2 a b
      _ = (a ^ (n + 1) * a) * (b ^ (n + 1) * b) := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          pow_succ a (n + 1), pow_succ b (n + 1)]
  have c2 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    simpa [mul_assoc] using
      congrArg (fun x : G => (a ^ (n + 1))⁻¹ * x * b⁻¹) e2
  have hcancel : b ^ n * (b * a) = b ^ n * (a * b) := by
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by simp [pow_succ, mul_assoc]
      _ = a * b ^ (n + 1) := c2
      _ = (a * b ^ n) * b := by simp [pow_succ, mul_assoc]
      _ = (b ^ n * a) * b := by rw [c1]
      _ = b ^ n * (a * b) := by simp [mul_assoc]
  exact (mul_left_cancel hcancel).symm
