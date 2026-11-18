import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (a b : G) (ha : a ^ 2 = a) (hb : b ^ 2 = b) (hc : a ^ 3 * b ^ 3 = a ^ 3 * b): a = b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rintro a b
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  have commute_pow (k : ℕ)
      (hk : ∀ x y : G, (x * y) ^ k = x ^ k * y ^ k)
      (hk1 : ∀ x y : G, (x * y) ^ (k + 1) = x ^ (k + 1) * y ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    have e0 := hk a b
    have e1 := hk1 a b
    simp only [pow_succ] at e1
    rw [e0] at e1
    apply mul_left_cancel (a := a ^ k)
    apply mul_right_cancel (b := b)
    simpa only [mul_assoc] using e1
  have h0 : b ^ n * a = a * b ^ n := commute_pow n hn hn1
  have h1 : b ^ (n + 1) * a = a * b ^ (n + 1) := commute_pow (n + 1) hn1 hn2
  have hba : b * a = a * b := by
    apply mul_left_cancel (a := b ^ n)
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by simp [pow_succ, mul_assoc]
      _ = a * b ^ (n + 1) := h1
      _ = a * (b ^ n * b) := by rw [pow_succ]
      _ = (a * b ^ n) * b := by rw [mul_assoc]
      _ = (b ^ n * a) * b := by rw [h0]
      _ = b ^ n * (a * b) := by rw [mul_assoc]
  exact hba.symm
