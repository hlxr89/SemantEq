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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (h : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have impossible (z : ℤ) (hz : IsPrimitiveRoot z p) : False := by
    have hz1 : z = 1 := by
      rcases (pow_eq_one_iff_of_ne_zero hp.out.ne_zero).mp hz.pow_eq_one with hz1 | ⟨hz1, heven⟩
      · exact hz1
      · exfalso
        rcases heven with ⟨k, hk⟩
        omega
    exact hz.ne_one hp.out.one_lt hz1
  constructor <;> intro ha
  · exact (impossible a ha).elim
  · exact (impossible (-a) ha).elim
