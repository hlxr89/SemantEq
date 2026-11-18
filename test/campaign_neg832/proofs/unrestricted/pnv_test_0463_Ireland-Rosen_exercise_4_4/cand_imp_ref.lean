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
  have impossible (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro hx
    have hx_one : x = 1 := by
      rw [← ZMod.pow_card x]
      exact hx.pow_eq_one
    subst x
    exact hp0.ne_one (Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by simp)))
  exact iff_of_false (impossible a) (impossible (-a))
