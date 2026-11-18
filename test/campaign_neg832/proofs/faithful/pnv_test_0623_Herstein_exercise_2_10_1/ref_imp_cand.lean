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
theorem dummy {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal] {p : ℕ} [hp : Fact p.Prime] {b : G} (hb : b ^ p = 1) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  have hb_ne_one : b ≠ 1 := by
    intro h
    apply hbA
    rw [h]
    exact A.one_mem
  have hord_dvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hb
  have hord : orderOf b = p :=
    (hp.out.eq_one_or_self_of_dvd (orderOf b) hord_dvd).resolve_left fun h =>
      hb_ne_one (orderOf_eq_one_iff.mp h)
  rw [Subgroup.zpowers_eq_closure]
  exact exercise_2_10_1_assumed A hbA (hord.symm ▸ hp.out)
