import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p a : ℕ} (hp : p.Prime) (h : p = 4 * a + 1) : IsPrimitiveRoot (-a : ℤ) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have not_primitive (x : ZMod p) : ¬IsPrimitiveRoot x p := by
    intro hx
    have hx_one : x = 1 := by
      rw [← ZMod.pow_card x]
      exact hx.pow_eq_one
    exact hx.ne_one hp0.one_lt hx_one
  constructor
  · intro hpos
    exact (not_primitive a hpos).elim
  · intro hneg
    exact (not_primitive (-a) hneg).elim
