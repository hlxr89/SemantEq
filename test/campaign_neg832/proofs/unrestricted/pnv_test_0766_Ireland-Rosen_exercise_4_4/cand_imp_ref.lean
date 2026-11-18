import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact p.Prime := ⟨hp0⟩
  letI : NeZero p := ⟨hp0.ne_zero⟩
  have no_root : ∀ b : ZMod p, ¬ IsPrimitiveRoot b p := by
    intro b hb
    have hn : NeZero ((p : ℕ) : ZMod p) := hb.neZero'
    exact hn.out (by simp)
  exact ⟨fun h ↦ (no_root a h).elim, fun h ↦ (no_root (-a) h).elim⟩
