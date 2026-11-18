import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (n : ℕ) (hp : p = 2^n + 1) (hfp : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  exfalso
  have hroot := dummy_assumed n hpn hp
  have hlt : 1 < 3 ^ p := Nat.one_lt_pow hp.ne_zero (by norm_num)
  have heq : 3 ^ p = 1 := hroot.pow_eq_one
  omega
