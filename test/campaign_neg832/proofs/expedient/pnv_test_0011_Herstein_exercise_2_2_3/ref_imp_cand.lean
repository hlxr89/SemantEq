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
  have hm := h (i - 1) (by simp)
  have hi := h i (by simp)
  have hp := h (i + 1) (by simp)
  have cm : Commute a (b ^ (i - 1)) := by
    apply (commute_iff_eq _ _).mpr
    symm
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ (i - 1))
    simpa only [mul_assoc] using
      (show a ^ (i - 1) * b ^ (i - 1) * (a * b) =
          (a ^ (i - 1) * a) * (b ^ (i - 1) * b) by
        calc
          _ = (a * b) ^ (i - 1) * (a * b) := by rw [hm]
          _ = (a * b) ^ i := by rw [← zpow_add_one]; congr 1 <;> omega
          _ = a ^ i * b ^ i := hi
          _ = _ := by
            have ha : a ^ i = a ^ (i - 1) * a := by
              rw [← zpow_add_one]
              congr 1 <;> omega
            have hb : b ^ i = b ^ (i - 1) * b := by
              rw [← zpow_add_one]
              congr 1 <;> omega
            rw [ha, hb])
  have ci : Commute a (b ^ i) := by
    apply (commute_iff_eq _ _).mpr
    symm
    apply mul_right_cancel (b := b)
    apply mul_left_cancel (a := a ^ i)
    simpa only [mul_assoc] using
      (show a ^ i * b ^ i * (a * b) = (a ^ i * a) * (b ^ i * b) by
        rw [← hi, ← zpow_add_one, ← zpow_add_one, ← zpow_add_one, hp])
  have hc := cm.inv_right.mul_right ci
  convert hc using 1 <;> group
