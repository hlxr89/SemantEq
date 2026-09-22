import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p : ℕ} {α : ℕ} [hp : Fact p.Prime] (hG : Fintype.card G = p ^ α) (hα : α ≠ 0) : ∀ H : Subgroup G, Subgroup.index H = p → Normal H := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_2_9a {G : Type*} [Fintype G] [Group G] {p α : ℕ}
  (hp : p.Prime) (ha : α > 0) (hG : card G = p ^ α) :
  ∀ H : Subgroup G, H.index = p → H.Normal := by
  letI : Fact p.Prime := ⟨hp⟩
  exact dummy_assumed hG (Nat.ne_of_gt ha)
