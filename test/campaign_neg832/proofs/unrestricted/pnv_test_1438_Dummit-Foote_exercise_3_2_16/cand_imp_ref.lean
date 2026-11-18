import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p a : ℕ) (hp : (p : ℕ) > 1) (ha : a < p) : a^p = a % p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  have hfalse : False := by
    have h := dummy_assumed 3 2 (by norm_num) (by norm_num)
    norm_num at h
  exact hfalse.elim
