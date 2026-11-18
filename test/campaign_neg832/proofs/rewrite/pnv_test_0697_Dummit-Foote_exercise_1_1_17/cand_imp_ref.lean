import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Group G] (x : G) {n : ℕ} (hn : 1 < n) : x⁻¹ = x^(n - 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  by_cases hn : 1 < (n : ℕ)
  · exact dummy_assumed x hn
  · have hn_one : (n : ℕ) = 1 :=
      Nat.le_antisymm (Nat.le_of_not_gt hn) n.property
    have hx_inv_two : x⁻¹ = x := by
      simpa only [Nat.reduceSub, pow_one] using
        (dummy_assumed x (n := 2) (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
    have hx_inv_three : x⁻¹ = x ^ 2 := by
      simpa only [Nat.reduceSub] using
        (dummy_assumed x (n := 3) (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
    have hx_square : x = x ^ 2 := hx_inv_two.symm.trans hx_inv_three
    have hx : x = 1 := by
      apply mul_left_cancel (a := x) -- non-rewrite step
      simpa only [pow_two, mul_one] using hx_square.symm
    have hn_sub : (n - 1 : ℕ) = 0 := by
      simp only [hn_one, Nat.reduceSub]
    rw [hn_sub, pow_zero, hx, inv_one]
