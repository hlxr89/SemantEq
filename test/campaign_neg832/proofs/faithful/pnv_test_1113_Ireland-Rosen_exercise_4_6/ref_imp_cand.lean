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
  -- not proved: the goal is over ℕ, while the assumption is over ZMod p, with no primitive-root equivalence between them
  sorry
