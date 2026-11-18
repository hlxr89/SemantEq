import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed { G : Type*} [Group G] {x : G} {n : ℕ} (hn : n > 0) (hnx : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  rw [← hxn]
  apply dummy_assumed
  · rw [hxn]
    exact n.prop
  · exact pow_orderOf_eq_one x
