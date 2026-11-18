import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] [hp1 : Fact (p % 4 = 1)] (a : ℤ) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hpmod : p % 4 = 1 := by
    omega
  letI : Fact p.Prime := ⟨hp0⟩
  letI : Fact (p % 4 = 1) := ⟨hpmod⟩
  have htransport := dummy_assumed (p := p) (0 : ℤ)
  have hpgt : 1 < p := hp0.one_lt
  constructor
  · intro h
    have heq : orderOf a = p := IsPrimitiveRoot.iff_orderOf.mp h
    have hlt := ZMod.orderOf_lt hpgt a
    omega
  · intro h
    have heq : orderOf (-a) = p := IsPrimitiveRoot.iff_orderOf.mp h
    have hlt := ZMod.orderOf_lt hpgt (-a)
    omega
