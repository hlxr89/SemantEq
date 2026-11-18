import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ) : a ^ p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let r : ℕ := (a % (p : ℤ)).toNat
  have hr_nonneg : 0 ≤ a % (p : ℤ) :=
    Int.emod_nonneg a (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hr_cast : (r : ℤ) = a % (p : ℤ) := by
    exact Int.toNat_of_nonneg hr_nonneg
  have h := dummy_assumed p r
  rw [← Int.natCast_modEq_iff, Int.natCast_pow] at h
  have ha : (r : ℤ) ≡ a [ZMOD p] := by
    rw [hr_cast]
    exact Int.mod_modEq a (p : ℤ)
  exact (ha.symm.pow p).trans (h.trans ha)
