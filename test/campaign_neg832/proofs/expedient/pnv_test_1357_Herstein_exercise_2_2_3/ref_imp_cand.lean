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
theorem dummy {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j : ℤ, j = i + 1 ∨ j = i + 2 → a * b ^ j = a ^ j * b ^ j) : Commute a b := by
  have ha1 : a = a ^ (i + 1) := mul_right_cancel (h (i + 1) (Or.inl rfl))
  have ha2 : a = a ^ (i + 2) := mul_right_cancel (h (i + 2) (Or.inr rfl))
  have haa : a = a * a := by
    calc
      a = a ^ (i + 2) := ha2
      _ = a ^ (i + 1) * a := by rw [show i + 2 = (i + 1) + 1 by ring, zpow_add]; simp
      _ = a * a := by rw [← ha1]
  have ha : a = 1 := by
    apply mul_right_cancel (b := a)
    simpa using haa
  simp [ha]
