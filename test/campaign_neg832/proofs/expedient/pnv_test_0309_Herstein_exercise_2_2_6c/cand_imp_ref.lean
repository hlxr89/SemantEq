import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {n : ℕ} (hn : 1 < n) (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) (a b : G) (hab : (a * b) ^ n = 1) : (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  intro a b
  have hn0 : 1 ≤ n := le_trans (by omega) hn
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn0
  have cross (x y : G) : x ^ (n - 1) * y ^ n = y ^ n * x ^ (n - 1) := by
    have xp : x ^ n = x ^ (n - 1) * x := by rw [← pow_succ, hn']
    have xip : (x⁻¹) ^ n = (x⁻¹) ^ (n - 1) * x⁻¹ := by rw [← pow_succ, hn']
    have hc : x * y ^ n * x⁻¹ = x ^ n * y ^ n * (x⁻¹) ^ n := by
      calc
        x * y ^ n * x⁻¹ = (x * y * x⁻¹) ^ n := by
          simpa only [MulAut.conj_apply] using (map_pow (MulAut.conj x) y n)
        _ = (x * y) ^ n * (x⁻¹) ^ n := h (x * y) x⁻¹
        _ = x ^ n * y ^ n * (x⁻¹) ^ n := by rw [h x y]
    symm
    calc
      y ^ n * x ^ (n - 1) = x⁻¹ * (x * y ^ n * x⁻¹) * x ^ n := by
        rw [xp]
        group
      _ = x⁻¹ * (x ^ n * y ^ n * (x⁻¹) ^ n) * x ^ n := by rw [hc]
      _ = x ^ (n - 1) * y ^ n := by
        rw [xp, xip]
        group
  have qanti (x y : G) : (x * y) ^ (n - 1) = y ^ (n - 1) * x ^ (n - 1) := by
    have zp : (x * y) ^ n = (x * y) ^ (n - 1) * (x * y) := by
      rw [← pow_succ, hn']
    have zp' : (x * y) ^ n = (x * y) * (x * y) ^ (n - 1) := by
      rw [← pow_succ', hn']
    have xp : x ^ n = x ^ (n - 1) * x := by rw [← pow_succ, hn']
    have yp : y ^ n = y ^ (n - 1) * y := by rw [← pow_succ, hn']
    calc
      (x * y) ^ (n - 1) = (x * y)⁻¹ * (x * y) ^ n := by
        rw [zp']
        exact (inv_mul_cancel_left (x * y) ((x * y) ^ (n - 1))).symm
      _ = (x * y)⁻¹ * (x ^ n * y ^ n) := by rw [h x y]
      _ = y ^ (n - 1) * x ^ (n - 1) := by
        rw [xp, show x ^ (n - 1) * x * y ^ n = x * (x ^ (n - 1) * y ^ n) by group,
          cross x y, yp]
        group
  let k := n * (n - 1)
  have tanti (x y : G) : (x * y) ^ k = y ^ k * x ^ k := by
    dsimp [k]
    rw [pow_mul, h x y, qanti, ← pow_mul, ← pow_mul]
  have tcomm (x y : G) : Commute (x ^ k) (y ^ k) := by
    dsimp [k]
    rw [pow_mul, show y ^ (n * (n - 1)) = (y ^ (n - 1)) ^ n by rw [pow_mul']]
    exact cross (x ^ n) (y ^ (n - 1))
  change (a * b * a⁻¹ * b⁻¹) ^ k = 1
  rw [tanti, tanti, tanti]
  simp only [inv_pow]
  rw [(tcomm a b).inv_mul_cancel_assoc]
  simp
