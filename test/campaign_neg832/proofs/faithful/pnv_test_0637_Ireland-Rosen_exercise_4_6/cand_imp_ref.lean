import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} {p : ℕ} (hp : p = 2^n + 1) (hprime : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  have hroot := dummy_assumed hpn hp
  have hp0 : p = 0 := by
    rw [hroot.eq_orderOf, orderOf_eq_zero_iff, isOfFinOrder_iff_isUnit]
    norm_num
  rw [hp0]
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_eq_zero_iff, isOfFinOrder_iff_isUnit]
  change ¬IsUnit ((3 : ℕ) : ZMod 0)
  rw [ZMod.isUnit_iff_coprime]
  norm_num
