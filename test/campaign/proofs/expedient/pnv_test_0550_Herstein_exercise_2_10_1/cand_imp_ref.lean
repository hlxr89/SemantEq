import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b ∉ A) (hb' : orderOf b = p) : A ⊓ Subgroup.closure {b} = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  letI : Fact (orderOf b).Prime := ⟨hp⟩
  exact dummy_assumed (p := orderOf b) (A := A) (inferInstance) hb rfl
