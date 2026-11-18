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
  letI : Fact p.Prime := ⟨hp0⟩
  have no_root : ∀ z : ZMod p, ¬ IsPrimitiveRoot z p := by
    intro z hz
    apply hz.ne_one hp0.one_lt
    rw [← ZMod.pow_card z, hz.pow_eq_one]
  exact ⟨fun h ↦ (no_root a h).elim, fun h ↦ (no_root (-a) h).elim⟩
