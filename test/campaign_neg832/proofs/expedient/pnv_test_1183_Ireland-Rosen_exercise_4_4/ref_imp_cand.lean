import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_assumed {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℕ} (hp : p = 4 * t + 1) (a : ℤ) (ha : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := by
  -- not proved: false when t = 0, p = 1, and a = 1
  sorry
