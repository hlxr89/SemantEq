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
  obtain ⟨p, hpG, hp⟩ := Nat.exists_infinite_primes (Nat.card G + 1)
  have hnot : ¬ p ∣ Nat.card G := by
    intro hdvd
    have hle : p ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := default
  have hcard : Nat.card P = 1 := by
    rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hnot, pow_zero]
  have hbot : (P : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp hcard
  refine ⟨p, hp, P, ?_⟩
  rw [hbot]
  infer_instance
