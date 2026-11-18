import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} {hk : Nat.Prime (p ^ (k + 1))} {x : ℤ} (hle : x ^ (p ^ (k + 1)) = 1) : ∃ (m : ℕ), 0 < m ∧ m < p ^ (k + 1) ∧ x ^ m = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  apply (Subgroup.eq_bot_iff_card (H ⊓ K)).2
  apply Nat.dvd_one.mp
  rw [← hHK.gcd_eq_one]
  apply Nat.dvd_gcd
  · simpa using
      (Subgroup.card_dvd_of_le (H := H ⊓ K) (K := H) inf_le_left)
  · simpa using
      (Subgroup.card_dvd_of_le (H := H ⊓ K) (K := K) inf_le_right)
