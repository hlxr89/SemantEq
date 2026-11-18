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
  let r := (a % (p : ℤ)).toNat
  have hr : (r : ℤ) = a % (p : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hp.ne_zero))
  have hcast : (r : ℤ) ^ p ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
    rw [← Int.natCast_pow, Int.natCast_modEq_iff]
    exact dummy_assumed
  have hrem : (r : ℤ) ≡ a [ZMOD (p : ℤ)] := by
    rw [hr]
    exact Int.mod_modEq a (p : ℤ)
  exact (hrem.symm.pow p).trans (hcast.trans hrem)
