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
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have impossible {x : ZMod p} (hx : IsPrimitiveRoot x p) : False := by
    have hxone : x = 1 := by
      rw [← ZMod.pow_card x, hx.pow_eq_one]
    exact (hx.ne_one hp0.one_lt) hxone
  constructor
  · intro ha
    exact (impossible ha).elim
  · intro hna
    exact (impossible hna).elim
