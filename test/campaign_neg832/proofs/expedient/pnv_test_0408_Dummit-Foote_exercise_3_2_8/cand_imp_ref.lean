import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {H K : Subgroup G} (hH : FiniteIndex H) (hK : FiniteIndex K) (hgcd : Nat.gcd H.index K.index = 1) : H ⊓ K = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  apply Subgroup.card_eq_one.mp
  apply Nat.dvd_one.mp
  rw [← hHK.gcd_eq_one]
  apply Nat.dvd_gcd
  · simpa only [Nat.card_eq_fintype_card] using
      (Subgroup.card_dvd_of_le inf_le_left : Nat.card ↥(H ⊓ K) ∣ Nat.card ↥H)
  · simpa only [Nat.card_eq_fintype_card] using
      (Subgroup.card_dvd_of_le inf_le_right : Nat.card ↥(H ⊓ K) ∣ Nat.card ↥K)
