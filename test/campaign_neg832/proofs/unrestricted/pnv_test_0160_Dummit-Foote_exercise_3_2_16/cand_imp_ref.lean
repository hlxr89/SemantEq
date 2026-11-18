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
  cases a with
  | ofNat n =>
      simpa using (Int.natCast_modEq_iff.mpr (dummy_assumed hp n))
  | negSucc n =>
      rw [Int.negSucc_eq]
      let m := n + 1
      have hmNat := dummy_assumed hp m
      have hm : (m : ℤ) ^ p ≡ (m : ℤ) [ZMOD p] := by
        exact_mod_cast hmNat
      rcases hp.eq_two_or_odd' with hp2 | hodd
      · subst p
        have hsign : (m : ℤ) ≡ -(m : ℤ) [ZMOD 2] := by
          rw [Int.modEq_iff_dvd]
          use -(m : ℤ)
          ring
        convert hm.trans hsign using 1 <;> simp [m] <;> ring_nf
      · have h := hm.neg
        rw [← hodd.neg_pow] at h
        convert h using 1 <;> simp [m] <;> ring
