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
theorem dummy (G : Type*) [Group G] (h : ∀ (a b : G) (i : ℕ), (a * b)^i = a^i * b^i → (a * b)^(i+1) = a^(i+1) * b^(i+1)) : ∀ a b : G, a * b = b * a := by
  intro a b
  have h2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := h a b 1 (by simp)
  have h' : b * (a * b) = a * (b * b) := by
    apply mul_left_cancel (a := a)
    simpa [pow_two, mul_assoc] using h2
  have hba : b * a = a * b := by
    apply mul_right_cancel (b := b)
    simpa [mul_assoc] using h'
  exact hba.symm
