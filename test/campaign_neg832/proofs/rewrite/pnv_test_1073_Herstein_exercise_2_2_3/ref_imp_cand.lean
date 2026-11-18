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
  apply exercise_2_2_3_assumed
    (P := λ i => ∀ x y : G, (x * y)^i = x^i * y^i) (hP := rfl)
  refine ⟨0, ?_, ?_, ?_⟩
  · intro x y
    simp only [pow_zero, mul_one]
  · intro x y
    simp only [Nat.zero_add, pow_one]
  · intro x y
    exact h x y 1 (by simp only [pow_one])
