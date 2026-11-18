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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have htransport := exercise_4_4_assumed hp.out (t := p / 4) (by omega) (a : ZMod p)
  constructor
  · intro ha
    have ha1 : a = 1 := by
      rcases (pow_eq_one_iff_of_ne_zero hp.out.ne_zero).mp ha.pow_eq_one with ha1 | ⟨_, heven⟩
      · exact ha1
      · rcases heven with ⟨k, hk⟩
        omega
    exact (ha.ne_one hp.out.one_lt ha1).elim
  · intro ha
    have ha1 : -a = 1 := by
      rcases (pow_eq_one_iff_of_ne_zero hp.out.ne_zero).mp ha.pow_eq_one with ha1 | ⟨_, heven⟩
      · exact ha1
      · rcases heven with ⟨k, hk⟩
        omega
    exact (ha.ne_one hp.out.one_lt ha1).elim

