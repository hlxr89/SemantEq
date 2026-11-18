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
theorem dummy {p : ℕ} [Fact (Nat.Prime p)] (hp1 : p = 4*t + 1) : IsPrimitiveRoot (-((4*t + 1 : ℕ) : ℤ)) p ↔ IsPrimitiveRoot ((4*t + 1 : ℕ) : ℤ) p := by
  have hp : Nat.Prime p := Fact.out
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hneg : ¬ IsPrimitiveRoot (-((4 * t + 1 : ℕ) : ℤ)) p := by
    intro h
    rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp h.pow_eq_one with hbase | ⟨hbase, _⟩
    · omega
    · apply hp.ne_one
      rw [hp1]
      exact_mod_cast (neg_inj.mp hbase)
  have hpos : ¬ IsPrimitiveRoot ((4 * t + 1 : ℕ) : ℤ) p := by
    intro h
    rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp h.pow_eq_one with hbase | ⟨hbase, _⟩
    · apply hp.ne_one
      rw [hp1]
      exact_mod_cast hbase
    · omega
  rcases exercise_4_4_assumed hp hp1 (0 : ZMod p) with ⟨_, _⟩
  exact ⟨fun h => (hneg h).elim, fun h => (hpos h).elim⟩
