import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p a : ℕ} (hp : Nat.Prime p) (hpa : p ∣ a) (h4a : 4 * a + 1 = p) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  -- not proved: the assumed statement only applies to integers satisfying unrelated and inconsistent divisibility/equality hypotheses, which cannot be supplied from the goal hypotheses
  sorry
