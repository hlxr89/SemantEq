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
  by_cases hn : 1 < (n : ℕ)
  · exact dummy_assumed x hn
  · have hn_one : (n : ℕ) = 1 := by
      have hn_pos : 0 < (n : ℕ) := n.2
      omega
    have hx : x = 1 := orderOf_eq_one_iff.mp (by simpa [hn_one] using hxn)
    have h := dummy_assumed x (n := 2) (by omega)
    simpa [hx, hn_one] using h
