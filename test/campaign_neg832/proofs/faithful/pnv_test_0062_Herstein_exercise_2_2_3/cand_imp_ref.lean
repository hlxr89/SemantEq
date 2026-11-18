import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (h : ∀ i : ℕ, (a * b) ^ (i + 2) = a ^ i * b ^ i * a ^ i * b ^ i) : a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rintro a b
  obtain ⟨n, hn, hn1, hn2⟩ := hP1
  have e0 := hn a b
  have e1 := hn1 a b
  have e2 := hn2 a b
  have hbn : b ^ n * a = a * b ^ n := by
    have ec : a ^ n * (b ^ n * a) * b = a ^ n * (a * b ^ n) * b := by
      calc
        a ^ n * (b ^ n * a) * b = (a * b) ^ (n + 1) := by
          rw [pow_succ, e0]
          simp [mul_assoc]
        _ = a ^ (n + 1) * b ^ (n + 1) := e1
        _ = a ^ n * (a * b ^ n) * b := by
          rw [pow_succ, pow_succ]
          simp [mul_assoc]
    let x := (a ^ n * (b ^ n * a))⁻¹ * a ^ n
    let y := a * b ^ n
    have ec' : a ^ n * (b ^ n * a) = a ^ n * (a * b ^ n) :=
      mul_right_cancel ec
    have hxy : x * y = 1 := by
      dsimp [x, y]
      rw [mul_assoc]
      change (a ^ n * (b ^ n * a))⁻¹ * (a ^ n * (a * b ^ n)) = 1
      rw [← ec']
      group
    have hd : x * y = y * x := dummy_assumed x y (by
      intro i
      have hx : x = y⁻¹ := mul_eq_one_iff_eq_inv.mp hxy
      rw [hxy, hx]
      simp)
    have hyx : y * x = 1 := by rw [← hd]; exact hxy
    dsimp [x, y] at hyx
    have hyx' : (a * b ^ n) * (b ^ n * a)⁻¹ = 1 := by
      simpa [mul_inv_rev, mul_assoc] using hyx
    symm
    calc
      a * b ^ n = (a * b ^ n) * (b ^ n * a)⁻¹ * (b ^ n * a) := by group
      _ = b ^ n * a := by rw [hyx', one_mul]
  have hbn1 : b ^ (n + 1) * a = a * b ^ (n + 1) := by
    have ec2 : a ^ (n + 1) * (b ^ (n + 1) * a) * b =
        a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
      calc
      a ^ (n + 1) * (b ^ (n + 1) * a) * b =
          (a ^ (n + 1) * b ^ (n + 1)) * (a * b) := by simp [mul_assoc]
      _ = (a * b) ^ (n + 1) * (a * b) := by rw [e1]
      _ = (a * b) ^ (n + 2) := by
        rw [show n + 2 = (n + 1) + 1 by omega]
        exact (pow_succ (a * b) (n + 1)).symm
      _ = a ^ (n + 2) * b ^ (n + 2) := e2
      _ = a ^ (n + 1) * (a * b ^ (n + 1)) * b := by
        rw [show n + 2 = (n + 1) + 1 by omega]
        simp only [pow_succ]
        simp [mul_assoc]
    exact mul_left_cancel (mul_right_cancel ec2)
  apply mul_left_cancel (a := b ^ n)
  calc
    b ^ n * (a * b) = (b ^ n * a) * b := by simp [mul_assoc]
    _ = (a * b ^ n) * b := by rw [hbn]
    _ = a * b ^ (n + 1) := by rw [pow_succ]; simp [mul_assoc]
    _ = b ^ (n + 1) * a := hbn1.symm
    _ = b ^ n * (b * a) := by rw [pow_succ]; simp [mul_assoc]
