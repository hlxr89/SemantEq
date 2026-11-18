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
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have no_zmod_root (x : ZMod p) (h : IsPrimitiveRoot x p) : False := by
    have hne : x ≠ 0 := (h.isUnit hp0.ne_zero).ne_zero
    have hpow : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
    have hdvd : p ∣ p - 1 := h.dvd_of_pow_eq_one (p - 1) hpow
    have hle : p ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp0.one_lt) hdvd
    omega
  constructor
  · intro h
    exact (no_zmod_root a h).elim
  · intro h
    exact (no_zmod_root (-a) h).elim
