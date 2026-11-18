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
  have hxpos : 0 < orderOf x := by simpa [hxn] using n.pos
  rw [← hxn]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel hxpos, pow_orderOf_eq_one]
