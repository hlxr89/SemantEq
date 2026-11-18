import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j : ℤ, j = i + 1 ∨ j = i + 2 → a * b ^ j = a ^ j * b ^ j) : Commute a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  rw [hP] at hP1
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  intro a b
  have habn : Commute a (b ^ n) := by
    have he : a ^ n * ((b ^ n * a) * b) = a ^ n * ((a * b ^ n) * b) := by
      calc
        a ^ n * ((b ^ n * a) * b) = a ^ n * b ^ n * (a * b) := by simp [mul_assoc]
        _ = (a * b) ^ n * (a * b) := by rw [hn a b]
        _ = (a * b) ^ (n + 1) := (pow_succ (a * b) n).symm
        _ = a ^ (n + 1) * b ^ (n + 1) := hn1 a b
        _ = a ^ n * ((a * b ^ n) * b) := by simp [pow_succ, mul_assoc]
    exact (mul_right_cancel (mul_left_cancel he)).symm
  have habn1 : Commute a (b ^ (n + 1)) := by
    have he : a ^ (n + 1) * ((b ^ (n + 1) * a) * b) =
        a ^ (n + 1) * ((a * b ^ (n + 1)) * b) := by
      calc
        a ^ (n + 1) * ((b ^ (n + 1) * a) * b) =
            a ^ (n + 1) * b ^ (n + 1) * (a * b) := by simp [mul_assoc]
        _ = (a * b) ^ (n + 1) * (a * b) := by rw [hn1 a b]
        _ = (a * b) ^ ((n + 1) + 1) := (pow_succ (a * b) (n + 1)).symm
        _ = (a * b) ^ (n + 2) := by congr 1 <;> omega
        _ = a ^ (n + 2) * b ^ (n + 2) := hn2 a b
        _ = a ^ (n + 1) * ((a * b ^ (n + 1)) * b) := by
          rw [show n + 2 = (n + 1) + 1 by omega]
          simp [pow_succ, mul_assoc]
    exact (mul_right_cancel (mul_left_cancel he)).symm
  have hone : Commute (1 : G) (b ^ n) := by
    apply dummy_assumed (a := (1 : G)) (b := b ^ n) (i := 0)
    intro j hj
    simp
  have he : b ^ n * (a * b) = b ^ n * (b * a) := by
    calc
      b ^ n * (a * b) = (a * b ^ n) * b := by rw [habn.eq]; simp [mul_assoc]
      _ = a * (b ^ n * b) := by simp [mul_assoc]
      _ = (b ^ n * b) * a := by simpa [pow_succ] using habn1.eq
      _ = b ^ n * (b * a) := by simp [mul_assoc]
  have he' : (1 * b ^ n) * (a * b) = (b ^ n * 1) * (b * a) := by
    calc
      (1 * b ^ n) * (a * b) = (b ^ n * 1) * (a * b) :=
        congrArg (fun x => x * (a * b)) hone.eq
      _ = (b ^ n * 1) * (b * a) := by simpa using he
  have he'' : b ^ n * (a * b) = b ^ n * (b * a) := by simpa using he'
  exact mul_left_cancel he''
