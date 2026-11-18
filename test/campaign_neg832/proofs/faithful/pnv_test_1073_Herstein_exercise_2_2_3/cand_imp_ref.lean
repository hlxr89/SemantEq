import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (h : ∀ (a b : G) (i : ℕ), (a * b)^i = a^i * b^i → (a * b)^(i+1) = a^(i+1) * b^(i+1)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  have consecutive_comm (k : ℕ)
      (hk : ∀ a b : G, (a * b) ^ k = a ^ k * b ^ k)
      (hks : ∀ a b : G, (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) :
      ∀ a b : G, b ^ k * a = a * b ^ k := by
    intro a b
    have heq : a ^ k * (b ^ k * a) * b = a ^ k * (a * b ^ k) * b := by
      calc
        a ^ k * (b ^ k * a) * b = (a * b) ^ k * (a * b) := by
          rw [hk]
          simp only [mul_assoc]
        _ = (a * b) ^ (k + 1) := (pow_succ (a * b) k).symm
        _ = a ^ (k + 1) * b ^ (k + 1) := hks a b
        _ = a ^ k * (a * b ^ k) * b := by simp only [pow_succ, mul_assoc]
    exact mul_left_cancel (mul_right_cancel heq)
  have hc_n : ∀ a b : G, b ^ n * a = a * b ^ n :=
    consecutive_comm n hn hn1
  have hc_n1 : ∀ a b : G, b ^ (n + 1) * a = a * b ^ (n + 1) :=
    consecutive_comm (n + 1) hn1 (by simpa [Nat.add_assoc] using hn2)
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    have heq : b ^ n * (b * a) = b ^ n * (a * b) := by
      calc
        b ^ n * (b * a) = b ^ (n + 1) * a := by simp only [pow_succ, mul_assoc]
        _ = a * b ^ (n + 1) := hc_n1 a b
        _ = (a * b ^ n) * b := by simp only [pow_succ, mul_assoc]
        _ = (b ^ n * a) * b := by rw [hc_n a b]
        _ = b ^ n * (a * b) := by simp only [mul_assoc]
    exact (mul_left_cancel heq).symm
  apply dummy_assumed G
  intro a b i hi
  calc
    (a * b) ^ (i + 1) = (a * b) ^ i * (a * b) := pow_succ (a * b) i
    _ = (a ^ i * b ^ i) * (a * b) := by rw [hi]
    _ = a ^ i * (b ^ i * a) * b := by simp only [mul_assoc]
    _ = a ^ i * (a * b ^ i) * b := by rw [hcomm (b ^ i) a]
    _ = a ^ (i + 1) * b ^ (i + 1) := by simp only [pow_succ, mul_assoc]
