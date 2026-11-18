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
  have hab_sq : (a * b) ^ 2 = 1 := by
    simpa using h0
  have hab_cube : (a * b) ^ 3 = a * b * a := by
    simpa [mul_assoc] using h1
  have ha : a = 1 := by
    have hs : a * b = a * b * a := by
      calc
        a * b = (a * b) ^ 2 * (a * b) := by simp [hab_sq]
        _ = (a * b) ^ 3 := by simp [pow_succ, mul_assoc]
        _ = a * b * a := hab_cube
    exact mul_left_cancel (a := a * b) (by simpa [mul_assoc] using hs)
  simp [ha]
