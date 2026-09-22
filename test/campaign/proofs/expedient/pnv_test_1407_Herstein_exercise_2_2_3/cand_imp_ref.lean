import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i+1) = a ^ (i+1) * b ^ (i+1) ∧ (a * b) ^ (i+2) = a ^ (i+2) * b ^ (i+2)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rcases hP1 with ⟨n, hn, hn₁, hn₂⟩
  intro a b
  have adjacent (j : ℕ)
      (e : (a * b) ^ j = a ^ j * b ^ j)
      (e' : (a * b) ^ (j + 1) = a ^ (j + 1) * b ^ (j + 1)) :
      b ^ j * a = a * b ^ j := by
    have E := e'
    rw [pow_succ, e, pow_succ, pow_succ] at E
    apply mul_left_cancel (a := a ^ j)
    apply mul_right_cancel (b := b)
    simpa only [mul_assoc] using E
  have c₀ := adjacent n (hn a b) (hn₁ a b)
  have hn₂' : (a * b) ^ ((n + 1) + 1) = a ^ ((n + 1) + 1) * b ^ ((n + 1) + 1) := by
    simpa only [add_assoc, one_add_one_eq_two] using hn₂ a b
  have c₁ := adjacent (n + 1) (hn₁ a b) hn₂'
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (b ^ n * a) * b := by simp only [mul_assoc]
    _ = (a * b ^ n) * b := by rw [c₀]
    _ = a * (b ^ n * b) := by simp only [mul_assoc]
    _ = (b ^ n * b) * a := by simpa only [pow_succ] using c₁.symm
    _ = b ^ n * (b * a) := by simp only [mul_assoc]
