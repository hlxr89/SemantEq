import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact (Nat.Prime p)] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have hpMod : p % 4 = 1 := by
    rw [hp1, Nat.mul_add_mod_self_left]
  have htransport := dummy_assumed hpMod (a.val : ℤ)
  have hpOne : 1 < p := hp0.one_lt
  constructor
  · intro ha
    have ha1 : a = 1 := by
      rw [← ZMod.pow_card a]
      exact ha.pow_eq_one
    exact (ha.ne_one hpOne ha1).elim -- non-rewrite step
  · intro hna
    have hna1 : -a = 1 := by
      rw [← ZMod.pow_card (-a)]
      exact hna.pow_eq_one
    exact (hna.ne_one hpOne hna1).elim -- non-rewrite step
