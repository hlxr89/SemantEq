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
  have hn : ∀ x : ZMod p, ¬IsPrimitiveRoot x p := by
    intro x h
    apply h.ne_one hp0.one_lt
    rw [← ZMod.pow_card x, h.pow_eq_one]
  exact ⟨fun h ↦ (hn a h).elim, fun h ↦ (hn (-a) h).elim⟩
