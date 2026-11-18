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
  -- not proved: the candidate's unannotated 3 has type ℕ, and no order-preserving cast bridge exists to ZMod p
  sorry
