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
  letI : Fact p.Prime := ⟨hp0⟩
  have impossible (x : ZMod p) (hx : IsPrimitiveRoot x p) : False := by
    have hx0 : x ≠ 0 := (hx.isUnit hp0.ne_zero).ne_zero
    have hd : p ∣ p - 1 := by
      simpa only [← hx.eq_orderOf] using ZMod.orderOf_dvd_card_sub_one hx0
    have hp_le : p ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp0.one_lt) hd
    omega
  constructor <;> intro ha
  · exact (impossible a ha).elim
  · exact (impossible (-a) ha).elim
