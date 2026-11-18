import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [Fact (Nat.Prime p)] (hp1 : p = 4*t + 1) : IsPrimitiveRoot (-((4*t + 1 : ℕ) : ℤ)) p ↔ IsPrimitiveRoot ((4*t + 1 : ℕ) : ℤ) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  letI : Fact (Nat.Prime p) := ⟨hp0⟩
  have hp_ne : p ≠ 0 := hp0.ne_zero
  have ha : ¬ IsPrimitiveRoot a p := by
    intro h
    apply h.ne_one hp0.one_lt
    calc
      a = a ^ p := (ZMod.pow_card a).symm
      _ = 1 := h.pow_eq_one
  have hna : ¬ IsPrimitiveRoot (-a) p := by
    intro h
    apply h.ne_one hp0.one_lt
    calc
      -a = (-a) ^ p := (ZMod.pow_card (-a)).symm
      _ = 1 := h.pow_eq_one
  have hneg : ¬ IsPrimitiveRoot (-((4 * t + 1 : ℕ) : ℤ)) p := by
    intro h
    rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp h.pow_eq_one with hbase | ⟨hbase, _⟩
    · omega
    · apply hp0.ne_one
      rw [hp1]
      exact_mod_cast (neg_inj.mp hbase)
  have hpos : ¬ IsPrimitiveRoot ((4 * t + 1 : ℕ) : ℤ) p := by
    intro h
    rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp h.pow_eq_one with hbase | ⟨hbase, _⟩
    · apply hp0.ne_one
      rw [hp1]
      exact_mod_cast hbase
    · omega
  simpa [ha, hna, hneg, hpos] using dummy_assumed (p := p) hp1
