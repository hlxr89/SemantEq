import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {x : G} {n : ℕ} (hx : x ^ n = 1) (hn : n ≠ 0) : x⁻¹ = x ^ (n - 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  have hon : orderOf x ≠ 0 := by
    rw [hxn]
    exact n.ne_zero
  have hc := dummy_assumed (x := x) (n := orderOf x)
    (pow_orderOf_eq_one x) hon
  simpa only [hxn] using hc
