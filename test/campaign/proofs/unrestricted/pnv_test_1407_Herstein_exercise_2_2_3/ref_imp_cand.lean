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
  obtain ⟨i, hi⟩ := h
  intro a b
  rcases hi a b with ⟨h0, h1, h2⟩
  have hc0 : b ^ i * a = a * b ^ i := by
    apply mul_left_cancel (a := a ^ i)
    apply mul_right_cancel (b := b)
    calc
      a ^ i * (b ^ i * a) * b = (a * b) ^ i * (a * b) := by
        rw [h0]
        simp only [mul_assoc]
      _ = (a * b) ^ (i + 1) := (zpow_add_one (a * b) i).symm
      _ = a ^ (i + 1) * b ^ (i + 1) := h1
      _ = a ^ i * (a * b ^ i) * b := by
        rw [zpow_add_one a i, zpow_add_one b i]
        simp only [mul_assoc]
  have hc1 : b ^ (i + 1) * a = a * b ^ (i + 1) := by
    apply mul_left_cancel (a := a ^ (i + 1))
    apply mul_right_cancel (b := b)
    calc
      a ^ (i + 1) * (b ^ (i + 1) * a) * b = (a * b) ^ (i + 1) * (a * b) := by
        rw [h1]
        simp only [mul_assoc]
      _ = (a * b) ^ ((i + 1) + 1) := (zpow_add_one (a * b) (i + 1)).symm
      _ = (a * b) ^ (i + 2) := by congr 1 <;> omega
      _ = a ^ (i + 2) * b ^ (i + 2) := h2
      _ = a ^ ((i + 1) + 1) * b ^ ((i + 1) + 1) := by congr 2 <;> omega
      _ = a ^ (i + 1) * (a * b ^ (i + 1)) * b := by
        rw [zpow_add_one a (i + 1), zpow_add_one b (i + 1)]
        simp only [mul_assoc]
  apply mul_left_cancel (a := b ^ i)
  calc
    b ^ i * (a * b) = (b ^ i * a) * b := by simp only [mul_assoc]
    _ = a * b ^ i * b := by rw [hc0]
    _ = a * b ^ (i + 1) := by rw [zpow_add_one b i]; simp only [mul_assoc]
    _ = b ^ (i + 1) * a := hc1.symm
    _ = b ^ i * (b * a) := by rw [zpow_add_one b i]; simp only [mul_assoc]
