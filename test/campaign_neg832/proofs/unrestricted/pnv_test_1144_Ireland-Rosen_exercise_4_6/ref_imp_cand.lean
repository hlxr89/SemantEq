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
theorem dummy {p : ℕ} (hp : ∃ n : ℕ, p = 2^n + 1 ∧ Nat.Prime p) : IsPrimitiveRoot 3 p := by
  have hbad := exercise_4_6_assumed (p := 2) (n := 0) (by norm_num) (by norm_num)
  have hdvd : 2 ∣ 1 := hbad.dvd_of_pow_eq_one 1 (by decide)
  norm_num at hdvd
