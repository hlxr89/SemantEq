import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_assumed {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {n : ℕ} {p : ℕ} (hp : p = 2^n + 1) (hprime : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  -- not proved: the only implication uses the inconsistent antecedent via forbidden impossible-case elimination
  sorry
