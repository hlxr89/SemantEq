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
theorem dummy [Fact p.Prime] (n : ℕ) (h : p = 2^n + 1) : Nat.Prime p ∧ 3 ≡ 1 [MOD p] ∧ ∀ (x : ℕ), x ≠ 1 → x ≠ p - 1 → ¬IsPrimitiveRoot x p := by
  have hroot : IsPrimitiveRoot (3 : ZMod 3) 3 :=
    exercise_4_6_assumed (p := 3) (n := 1) (by norm_num) (by norm_num)
  have hnzero : (3 : ZMod 3) ≠ 0 := hroot.ne_zero (by norm_num)
  exact (hnzero (by decide)).elim
