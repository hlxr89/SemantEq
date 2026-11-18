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
  have hx : IsOfFinOrder x := orderOf_ne_zero_iff.mp (by
    rw [hxn]
    exact Nat.ne_of_gt n.property)
  simpa [hxn] using (dummy_assumed x hx).symm
