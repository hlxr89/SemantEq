import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {a b : G} {n : ℕ} (h : ∀ (x y : G), (x * y) ^ n = x ^ n * y ^ n) (hab : Commute a b) (hba : Commute a (b ^ n) ) : Commute (a * b * a⁻¹ * b⁻¹) (a * b ^ n * a⁻¹ * b⁻¹) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  have hn0 : 0 < n := by omega
  have hn_eq : n = n - 1 + 1 := by omega
  have hcomm : ∀ x y : G, x ^ n * y ^ (n - 1) = y ^ (n - 1) * x ^ n := by
    intro x y
    have e := h (y * x) y⁻¹
    rw [conj_pow, h y x, inv_pow] at e
    have hy : y ^ n = y ^ (n - 1) * y := by
      conv_lhs => rw [hn_eq, pow_succ]
    rw [hy] at e
    have hcy : Commute (y ^ (n - 1)) y := (Commute.self_pow y (n - 1)).symm
    calc
      x ^ n * y ^ (n - 1) =
          y⁻¹ * (y * x ^ n * y⁻¹) * y * y ^ (n - 1) := by group
      _ = y⁻¹ * (y ^ (n - 1) * y * x ^ n *
          (y ^ (n - 1) * y)⁻¹) * y * y ^ (n - 1) := by rw [e]
      _ = y ^ (n - 1) * x ^ n := by
        rw [mul_inv_rev]
        rw [hcy.eq]
        group
  have hanti : ∀ x y : G, (x * y) ^ (n - 1) = y ^ (n - 1) * x ^ (n - 1) := by
    intro x y
    apply mul_right_cancel (b := x * y)
    rw [← pow_succ, ← hn_eq, h x y]
    rw [mul_assoc, ← mul_assoc (x ^ (n - 1)) x y, ← pow_succ, ← hn_eq]
    calc
      x ^ n * y ^ n = x ^ n * (y ^ (n - 1) * y) := by
        rw [← pow_succ, ← hn_eq]
      _ = (x ^ n * y ^ (n - 1)) * y := by rw [mul_assoc]
      _ = (y ^ (n - 1) * x ^ n) * y := by rw [hcomm]
      _ = y ^ (n - 1) * (x ^ n * y) := mul_assoc _ _ _
  intro a b
  have hr_comm : ∀ x y : G,
      x ^ (n * (n - 1)) * y ^ (n * (n - 1)) =
        y ^ (n * (n - 1)) * x ^ (n * (n - 1)) := by
    intro x y
    rw [pow_mul, pow_mul]
    have hc := hcomm (x ^ (n - 1)) (y ^ n)
    rw [← pow_mul] at hc
    simpa only [← pow_mul, Nat.mul_comm n (n - 1)] using hc
  rw [pow_mul]
  rw [h (a * b * a⁻¹) b⁻¹, h (a * b) a⁻¹, h a b]
  rw [inv_pow, inv_pow]
  rw [hanti, hanti, hanti]
  simp only [inv_pow]
  rw [← pow_mul, ← pow_mul]
  rw [← hr_comm a b]
  group
