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
  have ha1 : a = a ^ (i + 1) := by
    have hj := h (i + 1) (Or.inl rfl)
    exact mul_right_cancel hj
  have ha2 : a = a ^ (i + 2) := by
    have hj := h (i + 2) (Or.inr rfl)
    exact mul_right_cancel hj
  have ha : a = 1 := by
    have hs : a ^ (i + 2) = a ^ (i + 1) * a := by
      rw [show i + 2 = (i + 1) + 1 by omega, zpow_add_one]
    have haa : a = a * a := by
      calc
        a = a ^ (i + 2) := ha2
        _ = a ^ (i + 1) * a := hs
        _ = a * a := by rw [← ha1]
    have h1a : (1 : G) = a := by
      apply mul_left_cancel (a := a)
      simpa using haa
    exact h1a.symm
  letI : IsCyclic (Subgroup.zpowers b) := Subgroup.isCyclic_zpowers b
  letI : CommGroup (Subgroup.zpowers b) := IsCyclic.commGroup
  have hc : ∀ x y : Subgroup.zpowers b, x * y = y * x := by
    apply exercise_2_2_3_assumed
      (G := Subgroup.zpowers b)
      (P := fun n => ∀ x y : Subgroup.zpowers b, (x * y) ^ n = x ^ n * y ^ n)
      (hP := rfl)
    refine ⟨0, ?_, ?_, ?_⟩
    · intro x y
      exact (Commute.all x y).mul_pow 0
    · intro x y
      exact (Commute.all x y).mul_pow 1
    · intro x y
      exact (Commute.all x y).mul_pow 2
  rw [ha]
  exact congrArg Subtype.val (hc 1 ⟨b, Subgroup.mem_zpowers b⟩)
