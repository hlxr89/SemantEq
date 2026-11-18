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
theorem dummy {G : Type*} [Group G] {A : Subgroup G} [A.Normal] {b : G} {p : ℕ} [hp : Fact (Nat.Prime p)] (hb : b ^ p = 1) (hbnA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  have hdiv : orderOf b ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hb
  have hord : orderOf b = p := by
    rcases (Nat.dvd_prime hp.out).mp hdiv with hone | heq
    · have hb1 : b = 1 := orderOf_eq_one_iff.mp hone
      exact (hbnA (hb1 ▸ A.one_mem)).elim
    · exact heq
  have hprime : Nat.Prime (orderOf b) := hord.symm ▸ hp.out
  simpa only [Subgroup.zpowers_eq_closure] using
    (exercise_2_10_1_assumed A hbnA hprime)
