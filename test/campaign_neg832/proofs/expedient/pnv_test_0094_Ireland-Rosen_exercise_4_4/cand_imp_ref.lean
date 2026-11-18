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
  have no_root (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro hx
    have hlt := ZMod.orderOf_lt hp0.one_lt x
    rw [← hx.eq_orderOf] at hlt
    exact (Nat.lt_irrefl p) hlt
  exact iff_of_false (no_root a) (no_root (-a))
