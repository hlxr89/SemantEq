import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_2_2_3_assumed {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i * b ^ i) : a * b = b * a := by
  have h0 : (a * b) ^ 2 = 1 := by
    simpa using h 0
  have h1 : (a * b) ^ 3 = (a * b) ^ 2 := by
    simpa [pow_two, mul_assoc] using h 1
  have hab : a * b = 1 := by
    apply mul_left_cancel (a := (a * b) ^ 2)
    simpa [pow_succ, h0] using h1
  have hba : b * a = 1 := by
    rw [eq_inv_of_mul_eq_one_right hab, inv_mul_cancel]
  exact hab.trans hba.symm
