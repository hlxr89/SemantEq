import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ i = a^i * b^i) (i : ℕ) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  intro a b
  have commute_pow (k : ℕ)
      (hk : ∀ x y : G, (x * y) ^ k = x ^ k * y ^ k)
      (hk1 : ∀ x y : G, (x * y) ^ (k + 1) = x ^ (k + 1) * y ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    have e := hk1 a b
    rw [pow_succ, hk a b, pow_succ, pow_succ] at e
    have e' : a ^ k * (b ^ k * a) * b = a ^ k * (a * b ^ k) * b := by
      simpa [mul_assoc] using e
    exact mul_left_cancel (mul_right_cancel e')
  have hbn := commute_pow n hn hn1
  have hbn1 := commute_pow (n + 1) hn1 (by simpa [Nat.add_assoc] using hn2)
  have e : b ^ n * (b * a) = b ^ n * (a * b) := by
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by rw [pow_succ]; simp [mul_assoc]
      _ = a * b ^ (n + 1) := hbn1
      _ = (a * b ^ n) * b := by rw [pow_succ]; simp [mul_assoc]
      _ = (b ^ n * a) * b := by rw [hbn]
      _ = b ^ n * (a * b) := by rw [mul_assoc]
  exact (mul_left_cancel e).symm
