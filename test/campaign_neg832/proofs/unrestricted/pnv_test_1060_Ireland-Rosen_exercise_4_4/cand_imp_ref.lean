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
  haveI : Fact p.Prime := ⟨hp0⟩
  have no_root : ∀ x : ZMod p, ¬ IsPrimitiveRoot x p := by
    intro x hx
    have hxpow : x ^ p = 1 := hx.pow_eq_one
    rw [ZMod.pow_card] at hxpow
    subst x
    have : p = 1 := Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by simp))
    exact hp0.ne_one this
  simp only [no_root]
