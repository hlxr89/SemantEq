import Mathlib
open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal] {p : ℕ} [hp : Fact p.Prime] {b : G} (hb : b ^ p = 1) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  letI : Fact (Nat.Prime (orderOf b)) := ⟨hp⟩
  rw [← Subgroup.zpowers_eq_closure]
  exact dummy_assumed A (pow_orderOf_eq_one b) hb
