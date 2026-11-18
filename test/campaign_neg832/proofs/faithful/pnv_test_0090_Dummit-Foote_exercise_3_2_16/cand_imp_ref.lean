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
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hnat : a.natAbs ^ p ≡ a.natAbs [MOD p] := dummy_assumed
  have hpos : (a.natAbs : ℤ) ^ p ≡ (a.natAbs : ℤ) [ZMOD p] := by
    rw [Int.modEq_iff_dvd]
    rw [Nat.modEq_iff_dvd] at hnat
    simpa using hnat
  rcases Int.natAbs_eq a with ha | ha
  · rw [ha]
    exact hpos
  · rw [ha]
    rcases hp.eq_two_or_odd' with rfl | hpodd
    · have hsign : (-(a.natAbs : ℤ)) ≡ (a.natAbs : ℤ) [ZMOD (2 : ℕ)] := by
        rw [Int.modEq_iff_dvd]
        use a.natAbs
        ring
      exact (hsign.pow 2).trans (hpos.trans hsign.symm)
    · simpa only [Odd.neg_pow hpodd] using hpos.neg
