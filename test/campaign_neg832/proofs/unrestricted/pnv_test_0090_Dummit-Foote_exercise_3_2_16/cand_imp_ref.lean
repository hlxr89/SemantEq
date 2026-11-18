import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℕ} {p : ℕ} [hp : Fact (Nat.Prime p)] : a ^ p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  let n : ℕ := (a % (p : ℤ)).toNat
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hr : 0 ≤ a % (p : ℤ) := Int.emod_nonneg _ hp0
  have hn : (n : ℤ) = a % (p : ℤ) := by
    exact Int.toNat_of_nonneg hr
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hnat : n ^ p ≡ n [MOD p] := dummy_assumed
  have hint : (n : ℤ) ^ p ≡ (n : ℤ) [ZMOD (p : ℤ)] := by
    simpa only [Nat.cast_pow] using (Int.natCast_modEq_iff.mpr hnat)
  have ha : a ≡ (n : ℤ) [ZMOD (p : ℤ)] := by
    rw [hn]
    exact (Int.mod_modEq a (p : ℤ)).symm
  exact (ha.pow p).trans (hint.trans ha.symm)
