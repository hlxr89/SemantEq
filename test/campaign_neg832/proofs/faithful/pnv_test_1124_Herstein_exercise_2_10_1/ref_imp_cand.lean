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
theorem dummy {G : Type*} [Group G] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b^p = 1) (hp : Nat.Prime p) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  letI : A.Normal := hA
  have horder : Nat.Prime (orderOf b) := by
    have hdvd : orderOf b ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hb
    have hcases : orderOf b = 1 ∨ orderOf b = p :=
      hp.eq_one_or_self_of_dvd (orderOf b) hdvd
    have hne : orderOf b ≠ 1 := by
      intro h
      have hb_one : b = 1 := orderOf_eq_one_iff.mp h
      exact hbA (hb_one.symm ▸ A.one_mem)
    exact (hcases.resolve_left hne) ▸ hp
  simpa [Subgroup.zpowers_eq_closure] using
    (exercise_2_10_1_assumed A hbA horder)
