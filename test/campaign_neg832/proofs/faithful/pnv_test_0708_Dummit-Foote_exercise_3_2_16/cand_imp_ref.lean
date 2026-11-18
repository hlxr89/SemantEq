import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a^p ≡ a [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  let n : ℕ := (a % (p : ℤ)).toNat
  have hn := dummy_assumed p hp n
  have hn_int : (n : ℤ) ^ p ≡ (n : ℤ) [ZMOD (p : ℤ)] := by
    exact_mod_cast hn
  have hp_pos : (0 : ℤ) < (p : ℤ) := by
    exact_mod_cast hp.pos
  have hn_eq : (n : ℤ) = a % (p : ℤ) := by
    simp only [n, Int.toNat_of_nonneg (Int.emod_nonneg a hp_pos.ne')]
  have ha : a ≡ (n : ℤ) [ZMOD (p : ℤ)] := by
    rw [hn_eq]
    exact (Int.mod_modEq a (p : ℤ)).symm
  exact (ha.pow p).trans (hn_int.trans ha.symm)
