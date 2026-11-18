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
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrem_nonneg : 0 ≤ a % (p : ℤ) := Int.emod_nonneg a hpz
  let r : ℕ := (a % (p : ℤ)).toNat
  have hr : (r : ℤ) = a % (p : ℤ) := by
    simp [r, Int.toNat_of_nonneg hrem_nonneg]
  have hnat0 : r ^ p ≡ r [MOD p] := dummy_assumed p hp r
  have hnat : (r : ℤ) ^ p ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
    rw [← Int.natCast_modEq_iff] at hnat0
    simpa using hnat0
  have hmod : a % (p : ℤ) ≡ a [ZMOD (p : ℤ)] := Int.mod_modEq a (p : ℤ)
  rw [hr] at hnat
  exact (hmod.pow p).symm.trans (hnat.trans hmod)
