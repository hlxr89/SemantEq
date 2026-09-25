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
theorem dummy {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i + 1) = a ^ (i + 1) * b ^ (i + 1) ∧ (a * b) ^ (i + 2) = a ^ (i + 2) * b ^ (i + 2)) : ∀ a b : G, a * b = b * a := by
  rcases h with ⟨i, hi⟩
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    obtain ⟨hi0, hi1, hi2⟩ := hi a b
    have e1 := hi1
    rw [zpow_add (a * b) i 1, zpow_add a i 1, zpow_add b i 1] at e1
    simp only [zpow_one] at e1
    rw [hi0] at e1
    have hc0 : b ^ i * a = a * b ^ i := by
      apply mul_left_cancel (a := a ^ i)
      apply mul_right_cancel (b := b)
      simpa only [mul_assoc] using e1
    have e2 := hi2
    rw [show i + 2 = (i + 1) + 1 by
      simp only [add_assoc, one_add_one_eq_two]] at e2
    rw [zpow_add (a * b) (i + 1) 1, zpow_add a (i + 1) 1,
      zpow_add b (i + 1) 1] at e2
    simp only [zpow_one] at e2
    rw [hi1] at e2
    have hc1 : b ^ (i + 1) * a = a * b ^ (i + 1) := by
      apply mul_left_cancel (a := a ^ (i + 1))
      apply mul_right_cancel (b := b)
      simpa only [mul_assoc] using e2
    rw [zpow_add b i 1] at hc1
    simp only [zpow_one] at hc1
    apply mul_left_cancel (a := b ^ i)
    rw [← mul_assoc, hc0, mul_assoc]
    simpa only [mul_assoc] using hc1.symm
  apply exercise_2_2_3_assumed
    (P := λ i => ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i) (hP := rfl)
  refine ⟨0, ?_, ?_, ?_⟩
  · intro a b
    simp only [pow_zero, mul_one]
  · intro a b
    simp only [Nat.zero_add, pow_one]
  · intro a b
    simp only [Nat.zero_add]
    rw [pow_two, pow_two, pow_two]
    rw [← mul_assoc (a * b) a b, mul_assoc a b a, hcomm b a,
      ← mul_assoc a a b]
    exact mul_assoc (a * a) b b
