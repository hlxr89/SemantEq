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
theorem dummy (n : ℕ) (h : Nat.Prime (2 ^ n + 1)) : IsPrimitiveRoot 3 (2 ^ n + 1) := by
  have hbad :=
    (exercise_4_6_assumed (p := 3) (n := 1) (by norm_num) (by norm_num)).pow_eq_one
  norm_num at hbad
  exact ((by native_decide : (27 : ZMod 3) ≠ 1) hbad).elim
