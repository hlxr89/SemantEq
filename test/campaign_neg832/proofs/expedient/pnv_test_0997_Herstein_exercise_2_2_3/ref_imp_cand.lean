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
theorem dummy {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ i = a^i * b^i) (i : ℕ) : a * b = b * a := by
  have h2 := h 2
  have e : a * (b * a) * b = a * (a * b) * b := by
    simpa [pow_two, mul_assoc] using h2
  exact (mul_left_cancel (mul_right_cancel e)).symm
