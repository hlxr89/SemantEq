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
  let n := (a % p).toNat
  have h := dummy_assumed p n
  have hn : (n : ℤ) ^ p ≡ (n : ℤ) [ZMOD p] := by
    exact_mod_cast h
  have ha : (n : ℤ) = a % p := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hp.ne_zero))]
  have haMod : a ≡ (n : ℤ) [ZMOD p] := by
    unfold Int.ModEq
    rw [ha]
    exact (Int.emod_emod a p).symm
  exact (haMod.pow p).trans (hn.trans haMod.symm)
