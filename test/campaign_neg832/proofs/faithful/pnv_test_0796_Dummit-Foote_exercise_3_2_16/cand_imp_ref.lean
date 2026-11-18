import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact p.Prime] (a : ℕ) : a ^ p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  let r : ℕ := (a % (p : ℤ)).toNat
  have hpz : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hr_cast : (r : ℤ) = a % (p : ℤ) := by
    simp [r, Int.toNat_of_nonneg (Int.emod_nonneg a hpz)]
  have hr : (r ^ p : ℤ) ≡ (r : ℤ) [ZMOD (p : ℤ)] :=
    Int.natCast_modEq_iff.mpr (dummy_assumed p r)
  have ha : a ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
    rw [hr_cast]
    exact (Int.mod_modEq a (p : ℤ)).symm
  exact (ha.pow p).trans (hr.trans ha.symm)
