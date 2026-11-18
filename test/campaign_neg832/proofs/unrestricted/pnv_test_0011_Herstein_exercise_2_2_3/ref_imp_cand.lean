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
theorem dummy {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j ∈ ({i-1, i, i+1} : Finset ℤ), (a*b)^j = a^j * b^j) : Commute a b := by
  have hpow (x : G) (k : ℤ) : x ^ (k + 1) = x ^ k * x := by
    rw [zpow_add]
    simp
  have adjacent (k : ℤ)
      (hk : (a * b) ^ k = a ^ k * b ^ k)
      (hk1 : (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) :
      b ^ k * a = a * b ^ k := by
    apply mul_left_cancel (a := a ^ k)
    apply mul_right_cancel (b := b)
    calc
      a ^ k * (b ^ k * a) * b = (a ^ k * b ^ k) * (a * b) := by
        simp only [mul_assoc]
      _ = (a * b) ^ k * (a * b) := by rw [hk]
      _ = (a * b) ^ (k + 1) := (hpow (a * b) k).symm
      _ = a ^ (k + 1) * b ^ (k + 1) := hk1
      _ = (a ^ k * a) * (b ^ k * b) := by rw [hpow a k, hpow b k]
      _ = a ^ k * (a * b ^ k) * b := by
        simp only [mul_assoc]
  have him1 := h (i - 1) (by simp)
  have hi := h i (by simp)
  have hip1 := h (i + 1) (by simp)
  have hi' : (a * b) ^ ((i - 1) + 1) =
      a ^ ((i - 1) + 1) * b ^ ((i - 1) + 1) := by
    simpa only [sub_add_cancel] using hi
  have hc0 := adjacent (i - 1) him1 hi'
  have hc1 := adjacent i hi hip1
  apply mul_left_cancel (a := b ^ (i - 1))
  calc
    b ^ (i - 1) * (a * b) = (b ^ (i - 1) * a) * b := by
      simp only [mul_assoc]
    _ = (a * b ^ (i - 1)) * b := by rw [hc0]
    _ = a * b ^ i := by rw [mul_assoc, ← hpow]; congr 2 <;> omega
    _ = b ^ i * a := hc1.symm
    _ = (b ^ (i - 1) * b) * a := by rw [← hpow]; congr 2 <;> omega
    _ = b ^ (i - 1) * (b * a) := by simp only [mul_assoc]
