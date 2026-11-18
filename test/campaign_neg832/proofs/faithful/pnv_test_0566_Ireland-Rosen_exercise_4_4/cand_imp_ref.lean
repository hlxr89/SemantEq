import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p a : ℕ} (hp : Nat.Prime p) (hpa : p ∣ a) (h4a : 4 * a + 1 = p) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  -- not proved: the candidate antecedent requires incompatible divisibility and prime hypotheses and cannot be instantiated from this context
  sorry
