import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : a ^ p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnonneg : 0 ≤ a % (p : ℤ) := Int.emod_nonneg a (by exact_mod_cast hp.ne_zero)
  have hrep : (a % (p : ℤ)).toNat ^ p ≡ (a % (p : ℤ)).toNat [ZMOD p] := by
    have hnat := dummy_assumed p (a % (p : ℤ)).toNat
    have hcast := Int.natCast_modEq_iff.mpr hnat
    simpa only [Nat.cast_pow] using hcast
  have hcast : ((a % (p : ℤ)).toNat : ℤ) = a % (p : ℤ) := Int.toNat_of_nonneg hnonneg
  rw [hcast] at hrep
  exact (Int.ModEq.pow p (Int.mod_modEq a p)).symm.trans (hrep.trans (Int.mod_modEq a p))
