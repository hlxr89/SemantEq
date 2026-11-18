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
theorem dummy (p : ℕ) (hp : Nat.Prime p) (h : p = 2 ^ p + 1) : IsPrimitiveRoot 3 p := by
  -- not proved: the assumption concludes IsPrimitiveRoot in ZMod p, while this goal's unannotated 3 is inferred in ℕ
  sorry
