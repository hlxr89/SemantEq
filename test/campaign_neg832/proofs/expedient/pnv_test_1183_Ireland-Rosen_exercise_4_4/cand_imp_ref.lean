import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : p = 4 * t + 1) (a : ℤ) (ha : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have impossible (x : ZMod p) (hx : IsPrimitiveRoot x p) : False := by
    have hxp : x ^ p = 1 := hx.pow_eq_one
    rw [ZMod.pow_card] at hxp
    have hx1 : x = 1 := hxp
    subst x
    exact hp0.ne_one (hx.unique IsPrimitiveRoot.one)
  constructor
  · intro ha
    exact (impossible a ha).elim
  · intro ha
    exact (impossible (-a) ha).elim
