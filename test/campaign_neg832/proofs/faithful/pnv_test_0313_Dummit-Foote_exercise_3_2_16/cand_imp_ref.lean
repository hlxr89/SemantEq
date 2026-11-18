import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Nat.Prime p) (a : ℕ) : (a ^ p) % p = a % p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  let r : ℕ := (a % (p : ℤ)).toNat
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hr_nonneg : 0 ≤ a % (p : ℤ) := Int.emod_nonneg a hp0
  have hr_cast : (r : ℤ) = a % (p : ℤ) := by
    exact Int.toNat_of_nonneg hr_nonneg
  have ha : a ≡ (r : ℤ) [ZMOD p] := by
    change a % (p : ℤ) = (r : ℤ) % (p : ℤ)
    rw [hr_cast]
    exact (Int.emod_emod _ _).symm
  have hr_nat : r ^ p ≡ r [MOD p] := dummy_assumed hp r
  have hr_int : (r : ℤ) ^ p ≡ (r : ℤ) [ZMOD p] := by
    exact_mod_cast hr_nat
  exact ((ha.pow p).trans hr_int).trans ha.symm
