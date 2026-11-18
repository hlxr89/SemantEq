import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have hp_ne : p ≠ 0 := hp0.ne_zero
  have hp_one_lt : 1 < p := hp0.one_lt
  have hp_not_even : ¬ Even p := by
    rintro ⟨k, hk⟩
    omega
  have hp4 : p % 4 = 1 := by omega
  have hpos : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (a.val : ℤ) p := by
    constructor
    · intro ha
      have ha1 : a = 1 := by
        calc
          a = a ^ p := (ZMod.pow_card _).symm
          _ = 1 := ha.pow_eq_one
      exact (ha.ne_one hp_one_lt ha1).elim
    · intro ha
      rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp ha.pow_eq_one with ha1 | ⟨_, hp_even⟩
      · exact (ha.ne_one hp_one_lt ha1).elim
      · exact (hp_not_even hp_even).elim
  have hneg : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot (-(a.val : ℤ)) p := by
    constructor
    · intro ha
      have ha1 : -a = 1 := by
        calc
          -a = (-a) ^ p := (ZMod.pow_card _).symm
          _ = 1 := ha.pow_eq_one
      exact (ha.ne_one hp_one_lt ha1).elim
    · intro ha
      rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp ha.pow_eq_one with ha1 | ⟨_, hp_even⟩
      · exact (ha.ne_one hp_one_lt ha1).elim
      · exact (hp_not_even hp_even).elim
  exact hpos.trans (dummy_assumed hp4 (a.val : ℤ) |>.trans hneg.symm)
