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
  rcases h with ⟨i, hi⟩
  intro a b
  have e₀ := (hi a b).1
  have e₁ := (hi a b).2.1
  have e₂ := (hi a b).2.2
  have adjacent (j : ℤ)
      (e : (a * b) ^ j = a ^ j * b ^ j)
      (e' : (a * b) ^ (j + 1) = a ^ (j + 1) * b ^ (j + 1)) :
      b ^ j * a = a * b ^ j := by
    have E := e'
    rw [zpow_add_one, e, zpow_add_one, zpow_add_one] at E
    apply mul_left_cancel (a := a ^ j)
    apply mul_right_cancel (b := b)
    simpa only [mul_assoc] using E
  have c₀ := adjacent i e₀ e₁
  have e₂' : (a * b) ^ ((i + 1) + 1) = a ^ ((i + 1) + 1) * b ^ ((i + 1) + 1) := by
    simpa only [add_assoc, one_add_one_eq_two] using e₂
  have c₁ := adjacent (i + 1) e₁ e₂'
  apply mul_left_cancel (a := b ^ i)
  calc
    b ^ i * (a * b) = (b ^ i * a) * b := by simp only [mul_assoc]
    _ = (a * b ^ i) * b := by rw [c₀]
    _ = a * (b ^ i * b) := by simp only [mul_assoc]
    _ = (b ^ i * b) * a := by simpa only [zpow_add_one] using c₁.symm
    _ = b ^ i * (b * a) := by simp only [mul_assoc]
