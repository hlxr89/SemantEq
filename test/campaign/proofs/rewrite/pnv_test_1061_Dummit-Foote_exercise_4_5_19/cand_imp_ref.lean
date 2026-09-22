import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Fintype G] [DecidableEq G] (hG : Fintype.card G = 6545) : ¬IsSimpleGroup G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  classical
  exact dummy_assumed G hG
