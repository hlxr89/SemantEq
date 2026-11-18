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
theorem dummy {n : ℕ} {p : ℕ} (hp : p = 2^n + 1) (hprime : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  -- not proved: the candidate's `3` is in ℕ, whereas the antecedent's `3` is in ZMod p
  sorry
