import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {x : G} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  apply dummy_assumed
  · exact Nat.ne_of_gt n.pos
  · rw [← hxn]
    exact pow_orderOf_eq_one x
