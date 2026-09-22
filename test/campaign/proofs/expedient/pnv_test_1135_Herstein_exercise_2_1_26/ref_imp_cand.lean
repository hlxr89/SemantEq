import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_1_26_assumed {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] [Finite G] (a : G) : ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  letI := Fintype.ofFinite G
  obtain ⟨n, hn, ha⟩ := exercise_2_1_26_assumed a
  exact ⟨n, Nat.ne_of_gt hn, ha⟩
