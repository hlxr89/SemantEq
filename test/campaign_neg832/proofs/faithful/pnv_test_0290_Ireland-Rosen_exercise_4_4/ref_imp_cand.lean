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
theorem dummy {p : ℕ} (hp : Fact (Prime p)) (hp1 : p % 4 = 1) (hp3 : p ≠ 3) (a : ℤ) (ha : a.gcd p = 1) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  have hp_eq : p = 4 * (p / 4) + 1 := by omega
  have htransport := exercise_4_4_assumed hp.out.nat_prime hp_eq (a : ZMod p)
  have hp_ne : p ≠ 0 := hp.out.nat_prime.ne_zero
  have hp_not_even : ¬ Even p := by
    rintro ⟨k, hk⟩
    omega
  have no_int_root (x : ℤ) (_htransport :
      IsPrimitiveRoot (a : ZMod p) p ↔ IsPrimitiveRoot (-(a : ZMod p)) p) :
      ¬ IsPrimitiveRoot x p := by
    intro hx
    rcases (pow_eq_one_iff_of_ne_zero hp_ne).mp hx.pow_eq_one with rfl | ⟨rfl, heven⟩
    · have := hx.dvd_of_pow_eq_one 1 (by simp)
      exact hp.out.nat_prime.not_dvd_one this
    · exact hp_not_even heven
  exact ⟨fun h ↦ (no_int_root (-a) htransport h).elim,
    fun h ↦ (no_int_root a htransport h).elim⟩
