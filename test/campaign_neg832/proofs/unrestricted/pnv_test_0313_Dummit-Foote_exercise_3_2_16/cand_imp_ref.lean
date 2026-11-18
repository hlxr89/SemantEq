import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Nat.Prime p) (a : ℕ) : (a ^ p) % p = a % p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  rw [Int.cast_pow]
  letI : NeZero p := ⟨hp.ne_zero⟩
  let n := (a : ZMod p).val
  have hn : (n : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
  rw [← hn]
  have hmod : n ^ p ≡ n [MOD p] := dummy_assumed hp n
  have hint : (↑(n ^ p) : ℤ) ≡ ↑n [ZMOD ↑p] :=
    Int.natCast_modEq_iff.mpr hmod
  have hz : ((↑(n ^ p) : ℤ) : ZMod p) = ((↑n : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr hint
  simpa using hz
