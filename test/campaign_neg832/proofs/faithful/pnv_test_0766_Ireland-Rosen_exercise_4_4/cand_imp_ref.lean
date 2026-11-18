import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have hpmod : p % 4 = 1 := by omega
  have htransport := dummy_assumed hpmod (a.val : ℤ)
  constructor
  · intro ha
    have ha1 : a = 1 := (ZMod.pow_card a).symm.trans ha.pow_eq_one
    exact (ha.ne_one hp0.one_lt ha1).elim
  · intro ha
    have ha1 : -a = 1 := (ZMod.pow_card (-a)).symm.trans ha.pow_eq_one
    exact (ha.ne_one hp0.one_lt ha1).elim
