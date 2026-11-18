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
  have h1 := h (i + 1) (Or.inl rfl)
  have h2 := h (i + 2) (Or.inr rfl)
  have ha1 : a = a ^ (i + 1) := mul_right_cancel h1
  have ha2 : a = a ^ (i + 2) := mul_right_cancel h2
  have he : a ^ (i + 1) = a ^ (i + 2) := ha1.symm.trans ha2
  rw [show i + 2 = (i + 1) + 1 by omega, zpow_add_one a (i + 1)] at he
  have ha : a = 1 := by
    exact (mul_left_cancel (show a ^ (i + 1) * 1 = a ^ (i + 1) * a by simpa using he)).symm
  simp [ha]
