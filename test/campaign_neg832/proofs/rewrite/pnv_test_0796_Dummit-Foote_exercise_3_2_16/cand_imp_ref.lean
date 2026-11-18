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
  cases a with
  | ofNat n =>
      change (n : ℤ) ^ p ≡ (n : ℤ) [ZMOD p]
      exact_mod_cast dummy_assumed p n
  | negSucc n =>
      have h : ((n : ℤ) + 1) ^ p ≡ (n : ℤ) + 1 [ZMOD p] := by
        exact_mod_cast dummy_assumed p (n + 1)
      rcases hp.eq_two_or_odd with hp2 | hpodd
      · subst p
        have hsign : (n : ℤ) + 1 ≡ -((n : ℤ) + 1) [ZMOD 2] := by
          rw [Int.modEq_iff_dvd]
          refine ⟨-((n : ℤ) + 1), ?_⟩ -- non-rewrite step
          rw [show (2 : ℤ) = 1 + 1 by rfl, add_mul, one_mul]
          abel
        rw [Int.negSucc_eq,
          show (-((n : ℤ) + 1)) ^ 2 = ((n : ℤ) + 1) ^ 2 by
            simp only [pow_two, neg_mul_neg]]
        exact h.trans hsign
      · have hpOdd : Odd p := Nat.odd_iff.mpr hpodd
        rw [Int.negSucc_eq, hpOdd.neg_pow]
        exact h.neg
