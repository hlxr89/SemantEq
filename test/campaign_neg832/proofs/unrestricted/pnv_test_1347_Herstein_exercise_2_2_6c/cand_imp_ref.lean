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
  intro a b
  have hnform : n = (n - 1) + 1 := by omega
  have hpow (z : G) : z ^ n = z ^ (n - 1) * z := by
    conv_lhs => rw [hnform]
    rw [pow_succ]
  have hpow' (z : G) : z ^ n = z * z ^ (n - 1) := by
    conv_lhs => rw [hnform]
    rw [pow_succ']
  have hcomm : ∀ x y : G, Commute (x ^ (n - 1)) (y ^ n) := by
    intro x y
    have hconj : (y * x) ^ n = x⁻¹ * (x * y) ^ n * x := by
      rw [show y * x = x⁻¹ * (x * y) * x by group]
      simpa using (conj_pow (a := x⁻¹) (b := x * y) (i := n))
    rw [h y x, h x y] at hconj
    change x ^ (n - 1) * y ^ n = y ^ n * x ^ (n - 1)
    apply mul_right_cancel
    calc
      (x ^ (n - 1) * y ^ n) * x = (x⁻¹ * (x ^ n * y ^ n) * x) := by
        rw [hpow x]
        group
      _ = (y ^ n * x ^ n) := hconj.symm
      _ = (y ^ n * x ^ (n - 1)) * x := by
        rw [hpow x]
        simp [mul_assoc]
  have hanti : ∀ x y : G, (x * y) ^ (n - 1) = y ^ (n - 1) * x ^ (n - 1) := by
    intro x y
    have hc := (hcomm x y).eq
    calc
      (x * y) ^ (n - 1) = (x * y)⁻¹ * (x * y) ^ n := by
        rw [hpow' (x * y)]
        exact (inv_mul_cancel_left (x * y) ((x * y) ^ (n - 1))).symm
      _ = (x * y)⁻¹ * (x ^ n * y ^ n) := by rw [h x y]
      _ = y⁻¹ * (x ^ (n - 1) * y ^ n) := by
        rw [mul_inv_rev, hpow' x]
        group
      _ = y⁻¹ * (y ^ n * x ^ (n - 1)) := by rw [hc]
      _ = y ^ (n - 1) * x ^ (n - 1) := by
        rw [hpow' y]
        group
  have hkcomm : ∀ x y : G, Commute (x ^ (n * (n - 1))) (y ^ (n * (n - 1))) := by
    intro x y
    have hc := hcomm (x ^ n) (y ^ (n - 1))
    simpa only [← pow_mul, Nat.mul_comm] using hc
  have hk : ∀ x y : G, (x * y) ^ (n * (n - 1)) =
      x ^ (n * (n - 1)) * y ^ (n * (n - 1)) := by
    intro x y
    calc
      (x * y) ^ (n * (n - 1)) = ((x * y) ^ n) ^ (n - 1) := by rw [pow_mul]
      _ = (x ^ n * y ^ n) ^ (n - 1) := by rw [h x y]
      _ = (y ^ n) ^ (n - 1) * (x ^ n) ^ (n - 1) := hanti _ _
      _ = y ^ (n * (n - 1)) * x ^ (n * (n - 1)) := by rw [← pow_mul, ← pow_mul]
      _ = x ^ (n * (n - 1)) * y ^ (n * (n - 1)) := (hkcomm x y).eq.symm
  rw [hk, hk, hk]
  simp only [inv_pow]
  rw [(hkcomm a b).eq]
  group
