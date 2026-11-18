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
theorem dummy {p : ℕ} (h : Nat.Prime p ∧ ∃ (n : ℕ), p = 2^n + 1) : IsPrimitiveRoot 3 p := by
  have hbad : IsPrimitiveRoot (3 : ZMod 3) 3 :=
    exercise_4_6_assumed (p := 3) (n := 1) (by norm_num) (by norm_num)
  have hpw := hbad.pow_eq_one
  have hz : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [hz] at hpw
  norm_num at hpw
