import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Nat.Prime p) (a : ℕ) : a ^ p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  let r : ℕ := (a % (p : ℤ)).toNat
  have hr : (r : ℤ) = a % (p : ℤ) := by
    rw [show r = (a % (p : ℤ)).toNat from rfl, Int.toNat_of_nonneg]
    exact Int.emod_nonneg a (Int.ofNat_ne_zero.mpr hp.ne_zero)
  have hNatural : r ^ p ≡ r [MOD p] := dummy_assumed hp r
  have hCast : (r : ℤ) ^ p ≡ (r : ℤ) [ZMOD p] := by
    rw [← Int.natCast_pow]
    exact Int.natCast_modEq_iff.mpr hNatural
  have ha : a ≡ (r : ℤ) [ZMOD p] := by
    rw [hr]
    exact (Int.mod_modEq a (p : ℤ)).symm
  exact (ha.pow p).trans (hCast.trans ha.symm)
