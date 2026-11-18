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
  simpa [hxn] using dummy_assumed (pow_orderOf_eq_one x) (by
    rw [hxn]
    exact n.ne_zero)
