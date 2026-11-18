import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Fact p.Prime] (n : ℕ) (h : p = 2^n + 1) : Nat.Prime p ∧ 3 ≡ 1 [MOD p] ∧ ∀ (x : ℕ), x ≠ 1 → x ≠ p - 1 → ¬IsPrimitiveRoot x p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6 {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  -- not proved: at p = 2 and n = 0 the candidate conclusion holds, while the reference conclusion is false
  sorry
