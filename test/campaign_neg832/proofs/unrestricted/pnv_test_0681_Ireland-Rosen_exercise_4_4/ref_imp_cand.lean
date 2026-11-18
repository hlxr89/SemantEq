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
  have hp0 : Nat.Prime p := Fact.out
  have hpgt : 1 < p := hp0.one_lt
  have hpodd : Odd p := ⟨2 * t, by omega⟩
  constructor
  · intro h
    exfalso
    have hlt : (-((4*t + 1 : ℕ) : ℤ)) ^ p < 0 := hpodd.pow_neg (by omega)
    rw [h.pow_eq_one] at hlt
    omega
  · intro h
    exfalso
    have heq : ((4*t + 1 : ℕ) : ℤ) = 1 :=
      (pow_eq_one_iff_of_nonneg (by positivity) hp0.ne_zero).mp h.pow_eq_one
    omega
