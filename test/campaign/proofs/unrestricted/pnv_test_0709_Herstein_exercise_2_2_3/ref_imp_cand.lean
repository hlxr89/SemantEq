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
  obtain ⟨i, hi⟩ := h
  intro a b
  obtain ⟨h0, h1, h2⟩ := hi a b
  have hpow_i : b ^ i * a = a * b ^ i := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ i)
    simpa only [zpow_add_one, h0, mul_assoc] using h1
  have h2' :
      (a * b) ^ ((i + 1) + 1) =
        a ^ ((i + 1) + 1) * b ^ ((i + 1) + 1) := by
    simpa [add_assoc] using h2
  have hpow_i1 : b ^ (i + 1) * a = a * b ^ (i + 1) := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ (i + 1))
    simpa only [zpow_add_one, h1, mul_assoc] using h2'
  apply mul_left_cancel (a := b ^ i)
  calc
    b ^ i * (a * b) = (b ^ i * a) * b := by rw [mul_assoc]
    _ = (a * b ^ i) * b := by rw [hpow_i]
    _ = a * (b ^ i * b) := by rw [mul_assoc]
    _ = a * b ^ (i + 1) := by rw [zpow_add_one]
    _ = b ^ (i + 1) * a := hpow_i1.symm
    _ = (b ^ i * b) * a := by rw [zpow_add_one]
    _ = b ^ i * (b * a) := by rw [mul_assoc]
