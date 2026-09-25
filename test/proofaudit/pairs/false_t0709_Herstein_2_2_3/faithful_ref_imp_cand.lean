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
  have consecutive_bridge (k : ℤ)
      (hk : ∀ a b : G, (a * b) ^ k = a ^ k * b ^ k)
      (hk1 : ∀ a b : G, (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) :
      ∀ a b : G, b ^ k * a = a * b ^ k := by
    intro a b
    have e := hk1 a b
    rw [zpow_add_one (a * b) k, zpow_add_one a k, zpow_add_one b k, hk a b] at e
    have e' : a ^ k * ((b ^ k * a) * b) = a ^ k * ((a * b ^ k) * b) := by
      simpa only [mul_assoc] using e
    exact mul_right_cancel (mul_left_cancel e')
  have hki : ∀ a b : G, b ^ i * a = a * b ^ i :=
    consecutive_bridge i (fun a b => (hi a b).1) (fun a b => (hi a b).2.1)
  have hki1 : ∀ a b : G, b ^ (i + 1) * a = a * b ^ (i + 1) :=
    consecutive_bridge (i + 1) (fun a b => (hi a b).2.1) (by
      intro a b
      simpa only [Int.reduceAdd, add_assoc] using (hi a b).2.2)
  have hc : ∀ a b : G, a * b = b * a := by
    intro a b
    have e := hki1 a b
    rw [zpow_add_one b i] at e
    have e' : b ^ i * (b * a) = b ^ i * (a * b) := by
      calc
        b ^ i * (b * a) = b ^ i * b * a := by simp only [mul_assoc]
        _ = a * (b ^ i * b) := e
        _ = (a * b ^ i) * b := by simp only [mul_assoc]
        _ = (b ^ i * a) * b := by rw [hki a b]
        _ = b ^ i * (a * b) := by simp only [mul_assoc]
    exact (mul_left_cancel e').symm
  apply exercise_2_2_3_assumed (P := λ n => ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) (hP := rfl)
  refine ⟨0, ?_, ?_, ?_⟩
  · intro a b
    simp
  · intro a b
    simp
  · intro a b
    simp only [Nat.reduceAdd, pow_two]
    calc
      a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hc b a]
      _ = a * a * (b * b) := by simp only [mul_assoc]
