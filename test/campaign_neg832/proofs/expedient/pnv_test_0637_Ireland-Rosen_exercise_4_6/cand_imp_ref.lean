import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} {p : ℕ} (hp : p = 2^n + 1) (hprime : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  have h := dummy_assumed (n := 1) (p := 3) (by norm_num) (by norm_num)
  have hpow := h.pow_eq_one
  norm_num at hpow
