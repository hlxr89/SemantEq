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
  cases a with
  | ofNat n =>
      simpa only [Nat.cast_pow] using
        (Int.natCast_modEq_iff.mpr (dummy_assumed hp n))
  | negSucc n =>
      have hnat : (n + 1) ^ p ≡ n + 1 [MOD p] := dummy_assumed hp (n + 1)
      have hint : ((n + 1 : ℕ) : ℤ) ^ p ≡ ((n + 1 : ℕ) : ℤ) [ZMOD p] := by
        simpa only [Nat.cast_pow] using (Int.natCast_modEq_iff.mpr hnat)
      rcases hp.eq_two_or_odd' with rfl | hodd
      · simpa only [Int.negSucc_eq, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, pow_two, neg_mul_neg,
          Int.ModEq, Int.neg_emod_two] using hint
      · simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, hodd.neg_pow] using hint.neg
