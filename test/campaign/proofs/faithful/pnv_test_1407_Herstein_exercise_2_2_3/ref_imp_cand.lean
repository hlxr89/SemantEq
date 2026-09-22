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
  rcases h with ⟨i, hi⟩
  have htwo : ∀ a b : G, (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
    intro a b
    rcases hi a b with ⟨hi0, hi1, hi2⟩
    have e0 : a ^ i * b ^ i * (a * b) = (a ^ i * a) * (b ^ i * b) := by
      calc
        a ^ i * b ^ i * (a * b) = (a * b) ^ i * (a * b) := by rw [hi0]
        _ = (a * b) ^ (i + 1) := by rw [zpow_add_one]
        _ = a ^ (i + 1) * b ^ (i + 1) := hi1
        _ = (a ^ i * a) * (b ^ i * b) := by rw [zpow_add_one, zpow_add_one]
    have e1 : a ^ (i + 1) * b ^ (i + 1) * (a * b) =
        (a ^ (i + 1) * a) * (b ^ (i + 1) * b) := by
      calc
        a ^ (i + 1) * b ^ (i + 1) * (a * b) = (a * b) ^ (i + 1) * (a * b) := by rw [hi1]
        _ = (a * b) ^ (i + 2) := by
          rw [show i + 2 = (i + 1) + 1 by omega]
          exact (zpow_add_one (a * b) (i + 1)).symm
        _ = a ^ (i + 2) * b ^ (i + 2) := hi2
        _ = (a ^ (i + 1) * a) * (b ^ (i + 1) * b) := by
          rw [show i + 2 = (i + 1) + 1 by omega,
            zpow_add_one a (i + 1), zpow_add_one b (i + 1)]
    have r0 : b ^ i * a = a * b ^ i := by
      apply mul_left_cancel (a := a ^ i)
      apply mul_right_cancel (b := b)
      simpa only [mul_assoc] using e0
    have r1 : b ^ (i + 1) * a = a * b ^ (i + 1) := by
      apply mul_left_cancel (a := a ^ (i + 1))
      apply mul_right_cancel (b := b)
      simpa only [mul_assoc] using e1
    have hab : a * b = b * a := by
      apply mul_left_cancel (a := b ^ i)
      calc
        b ^ i * (a * b) = (b ^ i * a) * b := by simp only [mul_assoc]
        _ = (a * b ^ i) * b := by rw [r0]
        _ = a * (b ^ i * b) := by simp only [mul_assoc]
        _ = a * b ^ (i + 1) := by rw [zpow_add_one]
        _ = b ^ (i + 1) * a := r1.symm
        _ = (b ^ i * b) * a := by rw [zpow_add_one]
        _ = b ^ i * (b * a) := by simp only [mul_assoc]
    rw [pow_two, pow_two, pow_two]
    calc
      a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hab]
      _ = a * a * (b * b) := by simp only [mul_assoc]
  apply exercise_2_2_3_assumed (P := λ n => ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) (hP := rfl)
  exact ⟨0, by simp, by simp, htwo⟩
