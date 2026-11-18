import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∀ a b : G, ∀ i j k : ℤ, (a * b) ^ i * (a * b) ^ j = (a ^ i) * (b ^ i) * (a ^ j) * (b ^ j)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  rw [hP] at hP1
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  have consecutive (m : ℕ)
      (hm : ∀ a b : G, (a * b) ^ m = a ^ m * b ^ m)
      (hm1 : ∀ a b : G, (a * b) ^ (m + 1) = a ^ (m + 1) * b ^ (m + 1)) :
      ∀ a b : G, b ^ m * a = a * b ^ m := by
    intro a b
    have hs := hm1 a b
    rw [pow_succ, hm a b, pow_succ, pow_succ] at hs
    have hs' : b ^ m * (a * b) = a * (b ^ m * b) := by
      exact mul_left_cancel (by simpa only [mul_assoc] using hs)
    apply mul_right_cancel (b := b)
    simpa only [mul_assoc] using hs'
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    have hbna := consecutive n hn hn1 a b
    have hbn1a := consecutive (n + 1) hn1 (by simpa [Nat.add_assoc] using hn2) a b
    apply mul_left_cancel (a := b ^ n)
    calc
      b ^ n * (a * b) = (b ^ n * a) * b := by simp only [mul_assoc]
      _ = (a * b ^ n) * b := by rw [hbna]
      _ = a * (b ^ n * b) := by rw [mul_assoc]
      _ = a * b ^ (n + 1) := by rw [pow_succ]
      _ = b ^ (n + 1) * a := hbn1a.symm
      _ = b ^ n * (b * a) := by rw [pow_succ, mul_assoc]
  apply dummy_assumed
  intro a b i j k
  letI : CommGroup G := { inferInstanceAs (Group G) with
    mul_comm := hcomm }
  simp only [mul_zpow]
  ac_rfl
