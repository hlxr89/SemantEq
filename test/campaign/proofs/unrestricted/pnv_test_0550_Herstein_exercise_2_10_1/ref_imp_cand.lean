import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_10_1_assumed {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b ∉ A) (hb' : orderOf b = p) : A ⊓ Subgroup.closure {b} = ⊥ := by
  letI : A.Normal := hA
  apply exercise_2_10_1_assumed A hb
  simpa [hb'] using hp.out
