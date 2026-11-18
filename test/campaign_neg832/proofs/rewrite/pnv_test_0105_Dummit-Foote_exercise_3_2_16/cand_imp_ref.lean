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
  let b : ℕ := (a % (p : ℤ)).toNat
  have hb_nonneg : 0 ≤ a % (p : ℤ) :=
    Int.emod_nonneg a (by exact_mod_cast hp.ne_zero)
  have hb_cast : (b : ℤ) = a % (p : ℤ) := by
    exact Int.toNat_of_nonneg hb_nonneg
  have h_cand : (b : ℤ) ^ p ≡ (b : ℤ) [ZMOD p] := by
    rw [← Int.natCast_pow, Int.natCast_modEq_iff]
    exact dummy_assumed p b
  rw [hb_cast] at h_cand
  have h_mod : a % (p : ℤ) ≡ a [ZMOD p] := Int.mod_modEq a p
  exact ((h_mod.pow p).symm.trans h_cand).trans h_mod
