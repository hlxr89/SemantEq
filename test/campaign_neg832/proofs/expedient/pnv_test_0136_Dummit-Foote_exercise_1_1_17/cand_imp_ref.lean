import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (x : G)(n : ℕ) (hx : x ^ n = x) : x ^ (n-1) = x⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  have hpos : 0 < orderOf x := by
    rw [hxn]
    exact n.pos
  calc
    x⁻¹ = 1 * x⁻¹ := (one_mul _).symm
    _ = x ^ orderOf x * x⁻¹ := by rw [pow_orderOf_eq_one]
    _ = x ^ (orderOf x - 1) := by
      simpa only [pow_one] using (pow_sub x hpos).symm
    _ = x ^ (n - 1 : ℕ) := by rw [hxn]
