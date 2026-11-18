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
theorem dummy {p : ℕ} [hp : Fact (Nat.Prime p)] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hpOdd : Odd p := by
    exact Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hp1)
  have hpEq : p = 4 * (p / 4) + 1 := by
    exact (Nat.mod_add_div p 4).symm.trans (by rw [hp1, Nat.add_comm])
  have htransport := exercise_4_4_assumed (Fact.out : Nat.Prime p) hpEq (a : ZMod p)
  constructor
  · intro ha
    have ha1 : a = 1 := by
      apply hpOdd.strictMono_pow.injective
      simpa only [one_pow] using ha.pow_eq_one
    exact (ha.ne_one (Fact.out : Nat.Prime p).one_lt ha1).elim -- non-rewrite step
  · intro hna
    have hna1 : -a = 1 := by
      apply hpOdd.strictMono_pow.injective
      simpa only [one_pow] using hna.pow_eq_one
    exact (hna.ne_one (Fact.out : Nat.Prime p).one_lt hna1).elim -- non-rewrite step

