import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_17_assumed {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] {x : G} {n : ℕ} (hx : x ^ n = 1) (hn : 0 < n) : x⁻¹ = x ^ (n - 1) := by
  apply mul_left_cancel (a := x)
  rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hn, hx]
