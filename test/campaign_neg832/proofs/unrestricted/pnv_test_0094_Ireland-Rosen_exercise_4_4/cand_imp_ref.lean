import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (h : p.Prime) (hp : ∃ t : ℕ, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have impossible (x : ZMod p) (hx : IsPrimitiveRoot x p) : False := by
    have hx_one : x = 1 := by
      rw [← ZMod.pow_card x]
      exact hx.pow_eq_one
    apply hp0.ne_one
    rw [hx.eq_orderOf, hx_one]
    simp
  constructor
  · intro ha
    exact (impossible a ha).elim
  · intro hna
    exact (impossible (-a) hna).elim
