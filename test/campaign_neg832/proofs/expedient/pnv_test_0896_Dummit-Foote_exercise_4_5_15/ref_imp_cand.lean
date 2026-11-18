import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_5_15_assumed {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (G : Type*) [Group G] [Finite G] : ∃ (p : Nat) (hp : p.Prime) (P : Sylow p G), (P : Subgroup G).Normal := by
  obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (Nat.card G + 1)
  have hnd : ¬ p ∣ Nat.card G :=
    Nat.not_dvd_of_pos_of_lt Nat.card_pos (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := IsPGroup.of_bot.toSylow (by simpa using hnd)
  refine ⟨p, hp, P, ?_⟩
  change (⊥ : Subgroup G).Normal
  exact Subgroup.normal_bot
