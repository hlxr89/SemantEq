import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j : ℤ, j = i + 1 ∨ j = i + 2 → a * b ^ j = a ^ j * b ^ j) : Commute a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  have _hc : Commute (1 : G) 1 := dummy_assumed (1 : G) 1 0 (by
    intro j hj
    simp only [one_mul, one_zpow])
  rw [hP] at hP1
  obtain ⟨n, hn, hn₁, hn₂⟩ := hP1
  intro a b
  have e₀ := hn a b
  have e₁ := hn₁ a b
  have e₂ := hn₂ a b
  have hcomm₀ : b ^ n * a = a * b ^ n := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ n)
    simpa only [pow_succ, e₀, mul_assoc] using e₁
  have hcomm₁ : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ (n + 1))
    simpa only [pow_succ, e₁, mul_assoc] using e₂
  have hba : b * a = a * b := by
    apply mul_left_cancel (a := b ^ n)
    rw [pow_succ] at hcomm₁
    rw [← mul_assoc a (b ^ n) b, ← hcomm₀] at hcomm₁
    simpa only [mul_assoc] using hcomm₁
  exact hba.symm
