import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {n : ℕ} (hn : 2 < n) (h : ∀ a b : G, a * b * a⁻¹ * b⁻¹ = (a * b) ^ n → a * b = a * b) : ∀ a b : G, a * b * a⁻¹ * b⁻¹ = (a * b) ^ (n*(n-1)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  intro a b
  have h3 := dummy_assumed (G := G) (n := 3) (Nat.lt_succ_self 2)
    (fun x y _ => rfl) a b
  have h4 := dummy_assumed (G := G) (n := 4)
    (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))
    (fun x y _ => rfl) a b
  simp only [Nat.reduceMul, Nat.reduceSub] at h3 h4
  have hc : a * b * a⁻¹ * b⁻¹ = 1 := by
    rw [h3] at h4
    rw [show (12 : ℕ) = 6 * 2 by rfl, pow_mul] at h4
    apply mul_left_cancel (a := (a * b) ^ 6)
    rw [h3, mul_one, ← pow_two]
    exact h4.symm
  rw [hc, one_pow]
