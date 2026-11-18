import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Group G] (x : G) (hx : IsOfFinOrder x) : x ^ (orderOf x - 1) = x⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  symm
  apply (eq_inv_iff_mul_eq_one).2
  rw [← pow_succ, tsub_add_cancel_of_le (by exact n.prop), ← hxn, pow_orderOf_eq_one]
