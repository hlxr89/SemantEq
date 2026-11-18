import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : Fact (Prime p)) (hp1 : p % 4 = 1) (hp3 : p ≠ 3) (a : ℤ) (ha : a.gcd p = 1) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hp_mod : p % 4 = 1 := by omega
  have hp_ne_three : p ≠ 3 := by omega
  have _hcand := dummy_assumed (p := p) ⟨hp0.prime⟩ hp_mod hp_ne_three (a := 1) (by simp)
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have hp_pos : 0 < p := hp0.pos
  have not_primitive (x : ZMod p) : ¬ IsPrimitiveRoot x p := by
    intro hx
    have hx0 : x ≠ 0 := by
      intro hx_zero
      subst x
      have hzero : (0 : ZMod p) = 1 := by
        simpa [zero_pow hp_pos.ne'] using hx.pow_eq_one
      exact zero_ne_one hzero
    have hdvd : p ∣ p - 1 := by
      have horder := ZMod.orderOf_dvd_card_sub_one hx0
      rwa [← hx.eq_orderOf] at horder
    have hle : p ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp0.one_lt) hdvd
    omega
  exact ⟨fun h ↦ (not_primitive a h).elim, fun h ↦ (not_primitive (-a) h).elim⟩
