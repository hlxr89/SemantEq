import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p a : ℕ} (hp : p.Prime) (h : p = 4 * a + 1) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  -- not proved: the assumption only concerns the fixed natural parameter t in ℤ and supplies no statement about an arbitrary a : ZMod p
  sorry
