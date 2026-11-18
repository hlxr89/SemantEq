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
  intro a b
  have e0 := hn a b
  have e1 := hn1 a b
  have e2 := hn2 a b
  have commute_n : b ^ n * a = a * b ^ n := by
    have hcancel : a ^ n * (b ^ n * a) * b = a ^ n * (a * b ^ n) * b := by
      calc
        a ^ n * (b ^ n * a) * b = (a * b) ^ n * (a * b) := by
          rw [e0]
          simp only [mul_assoc]
        _ = (a * b) ^ (n + 1) := (pow_succ (a * b) n).symm
        _ = a ^ (n + 1) * b ^ (n + 1) := e1
        _ = a ^ n * (a * b ^ n) * b := by
          rw [pow_succ, pow_succ]
          simp only [mul_assoc]
    exact mul_left_cancel (mul_right_cancel hcancel)
  have commute_succ : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    have hcancel : a ^ (n + 1) * (b ^ (n + 1) * a) * b =
        a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
      calc
        a ^ (n + 1) * (b ^ (n + 1) * a) * b =
            (a * b) ^ (n + 1) * (a * b) := by
          rw [e1]
          simp only [mul_assoc]
        _ = (a * b) ^ (n + 2) := by
          simpa only [Nat.add_assoc] using (pow_succ (a * b) (n + 1)).symm
        _ = a ^ (n + 2) * b ^ (n + 2) := e2
        _ = a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
          have ha : a ^ (n + 2) = a ^ (n + 1) * a := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          have hb : b ^ (n + 2) = b ^ (n + 1) * b := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          rw [ha, hb]
          simp only [mul_assoc]
    exact mul_left_cancel (mul_right_cancel hcancel)
  have hfinal : b ^ n * (b * a) = b ^ n * (a * b) := by
    calc
      b ^ n * (b * a) = b ^ (n + 1) * a := by
        rw [pow_succ]
        simp only [mul_assoc]
      _ = a * b ^ (n + 1) := commute_succ
      _ = (a * b ^ n) * b := by
        rw [pow_succ]
        simp only [mul_assoc]
      _ = (b ^ n * a) * b := by rw [commute_n]
      _ = b ^ n * (a * b) := by simp only [mul_assoc]
  exact (mul_left_cancel hfinal).symm
