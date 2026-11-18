import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_2_3_assumed {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i) : a * b = b * a := by
  have h0 := h 0
  have h1 := h 1
  simp only [zero_add, pow_zero, mul_one] at h0
  norm_num at h1
  have hx3 : (a * b) ^ 3 = a * b := by
    rw [show 3 = 2 + 1 by omega, pow_add, h0]
    simp
  have ha : a = 1 := by
    have hab : a * b = (a * b) * a := hx3.symm.trans h1
    exact (mul_left_cancel (show (a * b) * 1 = (a * b) * a by simpa using hab)).symm
  simp [ha]
