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
  calc
    x⁻¹ = x⁻¹ * x ^ n := by rw [hx, mul_one]
    _ = x ^ (n - 1) := by
      nth_rewrite 1 [← Nat.sub_add_cancel hn]
      simp [pow_succ']
