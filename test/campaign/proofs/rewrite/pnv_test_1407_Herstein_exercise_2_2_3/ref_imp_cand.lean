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
theorem dummy {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i+1) = a ^ (i+1) * b ^ (i+1) ∧ (a * b) ^ (i+2) = a ^ (i+2) * b ^ (i+2)) : ∀ a b : G, a * b = b * a := by
  obtain ⟨i, h⟩ := h
  have hall : ∀ a b : G, a * b = b * a := by
    intro a b
    obtain ⟨h₀, h₁, h₂⟩ := h a b
    have step (j : ℤ)
        (hj : (a * b) ^ j = a ^ j * b ^ j)
        (hj₁ : (a * b) ^ (j + 1) = a ^ (j + 1) * b ^ (j + 1)) :
        b ^ j * a = a * b ^ j := by
      have hx := hj₁
      simp only [zpow_add, zpow_one] at hx
      rw [hj] at hx
      have hx' : b ^ j * (a * b) = a * (b ^ j * b) := mul_left_cancel (by
        simpa only [mul_assoc] using hx)
      exact mul_right_cancel (by
        simpa only [← mul_assoc] using hx')
    have hi := step i h₀ h₁
    have hi₁ := step (i + 1) h₁ (by
      simpa only [add_assoc, one_add_one_eq_two] using h₂)
    have hb : b ^ (i + 1) = b ^ i * b := by
      simpa only [zpow_one] using zpow_add b i 1
    apply Eq.symm
    apply mul_left_cancel (a := b ^ i)
    rw [← mul_assoc, ← hb, hi₁, hb]
    simp only [← mul_assoc]
    rw [hi]
  intro a b
  apply exercise_2_2_3_assumed
    (P := λ n => ∀ x y : G, (x * y) ^ n = x ^ n * y ^ n)
    (hP := rfl) (a := a) (b := b)
  refine ⟨0, ?_, ?_, ?_⟩
  · intro x y
    exact (show Commute x y from hall x y).mul_pow 0
  · intro x y
    exact (show Commute x y from hall x y).mul_pow 1
  · intro x y
    exact (show Commute x y from hall x y).mul_pow 2
