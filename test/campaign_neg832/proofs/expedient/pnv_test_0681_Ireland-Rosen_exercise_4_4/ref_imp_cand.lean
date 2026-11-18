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
  constructor <;> intro h
  all_goals
    exfalso
    have heq := congrArg Int.natAbs h.pow_eq_one
    simp [Int.natAbs_pow, hp1] at heq
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hle : p ≤ p ^ p := Nat.le_pow (by omega)
    omega
