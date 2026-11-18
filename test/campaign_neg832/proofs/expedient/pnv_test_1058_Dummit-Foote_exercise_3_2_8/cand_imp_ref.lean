import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (H K : Subgroup G) (hH : Finite H) (hK : Finite K) (hcop : IsCoprime (H.index : ℕ) (K.index)) : H ⊓ K = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall (H ⊓ K)).2
  intro x hx
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hHK
  · simpa [Nat.card_eq_fintype_card] using
      Subgroup.orderOf_dvd_natCard H (Subgroup.mem_inf.mp hx).1
  · simpa [Nat.card_eq_fintype_card] using
      Subgroup.orderOf_dvd_natCard K (Subgroup.mem_inf.mp hx).2
