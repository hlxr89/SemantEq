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
  have adjacent_comm (k : ℕ)
      (hk : ∀ x y : G, (x * y) ^ k = x ^ k * y ^ k)
      (hk1 : ∀ x y : G, (x * y) ^ (k + 1) = x ^ (k + 1) * y ^ (k + 1))
      (x y : G) : y ^ k * x = x * y ^ k := by
    have heq := hk1 x y
    rw [pow_succ, hk x y, pow_succ, pow_succ] at heq
    have hc := congrArg (fun z => (x ^ k)⁻¹ * z * y⁻¹) heq
    simpa [mul_assoc] using hc
  intro a b
  have hc_n : b ^ n * a = a * b ^ n := adjacent_comm n hn hn1 a b
  have hc_n1 : b ^ (n + 1) * a = a * b ^ (n + 1) := adjacent_comm (n + 1) hn1 hn2 a b
  have heq : b ^ n * (b * a) = b ^ n * (a * b) := by
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by simp [pow_succ, mul_assoc]
      _ = a * b ^ (n + 1) := hc_n1
      _ = (a * b ^ n) * b := by simp [pow_succ, mul_assoc]
      _ = (b ^ n * a) * b := by rw [hc_n]
      _ = b ^ n * (a * b) := by simp [mul_assoc]
  exact (mul_left_cancel heq).symm
