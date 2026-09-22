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
  intro a b
  have step (k : ℤ)
      (hk : ∀ x y : G, (x * y) ^ k = x ^ k * y ^ k)
      (hk1 : ∀ x y : G, (x * y) ^ (k + 1) = x ^ (k + 1) * y ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    have he : a ^ k * b ^ k * (a * b) = a ^ k * a * (b ^ k * b) := by
      calc
        a ^ k * b ^ k * (a * b) = (a * b) ^ k * (a * b) := by rw [hk a b]
        _ = (a * b) ^ (k + 1) := by rw [zpow_add_one]
        _ = a ^ (k + 1) * b ^ (k + 1) := hk1 a b
        _ = a ^ k * a * (b ^ k * b) := by rw [zpow_add_one, zpow_add_one, mul_assoc]
    have he' : b ^ k * a * b = a * b ^ k * b := by
      apply mul_left_cancel (a := a ^ k)
      simpa only [mul_assoc] using he
    exact mul_right_cancel he'
  have h0 := step i (fun x y => (hi x y).1) (fun x y => (hi x y).2.1)
  have h1 := step (i + 1) (fun x y => (hi x y).2.1) (fun x y => by simpa [add_assoc] using (hi x y).2.2)
  apply mul_left_cancel (a := b ^ i)
  calc
    b ^ i * (a * b) = (b ^ i * a) * b := by simp only [mul_assoc]
    _ = (a * b ^ i) * b := by rw [h0]
    _ = a * b ^ (i + 1) := by rw [zpow_add_one, mul_assoc]
    _ = b ^ (i + 1) * a := h1.symm
    _ = b ^ i * (b * a) := by rw [zpow_add_one, mul_assoc]
