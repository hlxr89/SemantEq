import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a^p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  let r : ℕ := (a % (p : ℤ)).toNat
  have hp0 : (p : ℤ) ≠ 0 := by
    intro h
    exact hp.ne_zero (Int.ofNat_inj.mp h)
  have hr : (r : ℤ) = a % (p : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg a hp0)
  have hnat := dummy_assumed p hp r
  have hint : (r : ℤ) ^ p ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
    rw [← Int.natCast_pow]
    exact Int.natCast_modEq_iff.mpr hnat
  have har : a ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
    rw [hr]
    exact (Int.mod_modEq a (p : ℤ)).symm
  exact (har.pow p).trans (hint.trans har.symm)
