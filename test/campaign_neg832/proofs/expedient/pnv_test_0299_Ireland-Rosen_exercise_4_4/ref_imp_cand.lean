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
theorem dummy (p : ℕ) [Fact (Nat.Prime p)] (hp : (p : ℤ) = 4*t+1) (a : ℤ) (hap : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := by
  have hp_ne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  rcases Int.isUnit_iff.mp (hap.isUnit hp_ne) with rfl | rfl
  · have h : p = 1 := hap.unique IsPrimitiveRoot.one
    exact ((Fact.out : Nat.Prime p).ne_one h).elim
  · have hneg : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by omega)
    have h : p = 2 := hap.unique hneg
    omega
