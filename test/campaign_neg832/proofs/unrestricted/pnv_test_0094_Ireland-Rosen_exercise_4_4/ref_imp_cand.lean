import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_assumed {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℕ} (h : p.Prime) (hp : ∃ t : ℕ, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  obtain ⟨t, rfl⟩ := hp
  have hp_ne_zero : 4 * t + 1 ≠ 0 := by omega
  have hp_ne_one : 4 * t + 1 ≠ 1 := h.ne_one
  have hp_ne_two : 4 * t + 1 ≠ 2 := by omega
  have impossible (x : ℤ) (hx : IsPrimitiveRoot x (4 * t + 1)) : False := by
    have hx_unit : IsUnit x := hx.isUnit hp_ne_zero
    rcases (Int.isUnit_iff.mp hx_unit) with rfl | rfl
    · apply hp_ne_one
      simpa using hx.eq_orderOf
    · apply hp_ne_two
      simpa using hx.eq_orderOf
  constructor
  · intro ha
    exact (impossible a ha).elim
  · intro hna
    exact (impossible (-a) hna).elim
