import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_assumed {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℕ} (n : ℕ) (hp : p = 2^n + 1) (hfp : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  exfalso
  have h := exercise_4_6_assumed (p := 3) (n := 1) (by norm_num) (by norm_num)
  have hh := h.pow_eq_one
  have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [h3] at hh
  norm_num at hh
