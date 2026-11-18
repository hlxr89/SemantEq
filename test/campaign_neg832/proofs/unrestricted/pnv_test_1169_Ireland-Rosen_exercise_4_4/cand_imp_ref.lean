import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (h : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  have no_root : ∀ x : ZMod p, ¬ IsPrimitiveRoot x p := by
    intro x hx
    have hx1 : x = 1 := by
      calc
        x = x ^ p := (ZMod.pow_card x).symm
        _ = 1 := hx.pow_eq_one
    exact hx.ne_one hp0.one_lt hx1
  exact ⟨fun ha ↦ (no_root a ha).elim, fun hna ↦ (no_root (-a) hna).elim⟩
