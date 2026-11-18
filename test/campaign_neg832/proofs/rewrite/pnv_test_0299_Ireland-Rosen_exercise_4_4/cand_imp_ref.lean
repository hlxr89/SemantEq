import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact (Nat.Prime p)] (hp : (p : ℤ) = 4*t+1) (a : ℤ) (hap : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  -- not proved: the integer implication has no hypothesis or conclusion about residue classes, and exact order cannot be lifted through ℤ → ZMod p
  sorry
