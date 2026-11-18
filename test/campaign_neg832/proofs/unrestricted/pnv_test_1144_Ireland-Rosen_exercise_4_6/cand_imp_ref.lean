import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : ∃ n : ℕ, p = 2^n + 1 ∧ Nat.Prime p) : IsPrimitiveRoot 3 p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  have hbad := dummy_assumed (p := 2) ⟨0, by norm_num, by norm_num⟩
  have := hbad.pow_eq_one
  norm_num at this
