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
theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have hp_prime : p.Prime := hp.out
  have hp_odd : ¬ Even p := by
    rintro ⟨k, hk⟩
    omega
  have impossible (x : ℤ) : ¬ IsPrimitiveRoot x p := by
    intro hx
    rcases (pow_eq_one_iff_of_ne_zero hp_prime.ne_zero).mp hx.pow_eq_one with rfl | ⟨rfl, he⟩
    · exact hp_prime.ne_one (Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by simp)))
    · exact hp_odd he
  exact iff_of_false (impossible a) (impossible (-a))
