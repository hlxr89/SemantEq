import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : p.Prime) (h : ∃ t, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have not_primitive (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro hx
    apply hx.ne_one hp0.one_lt
    calc
      x = x ^ p := (ZMod.pow_card x).symm
      _ = 1 := hx.pow_eq_one
  exact iff_of_false (not_primitive a) (not_primitive (-a))
