import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_2_9a_assumed {G : Type*} [Fintype G] [Group G] {p α : ℕ}
  (hp : p.Prime) (ha : α > 0) (hG : card G = p ^ α) :
  ∀ H : Subgroup G, H.index = p → H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] [Fintype G] {p : ℕ} {α : ℕ} [hp : Fact p.Prime] (hG : Fintype.card G = p ^ α) (hα : α ≠ 0) : ∀ H : Subgroup G, Subgroup.index H = p → Normal H := by
  exact exercise_4_2_9a_assumed hp.out (Nat.pos_of_ne_zero hα) hG
