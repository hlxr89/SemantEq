import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_17_assumed {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy { G : Type*} [Group G] {x : G} {n : ℕ} (hn : n > 0) (hnx : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel hn, hnx]
