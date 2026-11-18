import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] [hp1 : Fact (p % 4 = 1)] (a : ℤ) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have hp2 : 1 < p := by
    have := hp0.two_le
    omega
  have no_root (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro h
    have hx : x = 1 := by
      rw [← ZMod.pow_card x, h.pow_eq_one]
    exact h.ne_one hp2 hx
  exact iff_of_false (no_root a) (no_root (-a))
