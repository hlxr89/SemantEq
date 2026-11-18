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
theorem dummy {p : ℕ} [hp : Fact p.Prime] [hp1 : Fact (p % 4 = 1)] (a : ℤ) : IsPrimitiveRoot (-a) p ↔ IsPrimitiveRoot a p := by
  have hp_ne_two : p ≠ 2 := by
    intro h
    subst p
    have hbad : (2 : ℕ) = 1 := by
      simpa only [Nat.reduceMod] using hp1.out
    exact (Nat.ne_of_gt Nat.one_lt_two) hbad
  have hp_eq : p = 4 * (p / 4) + 1 := by
    rw [← hp1.out]
    simpa only [Nat.add_comm] using (Nat.mod_add_div p 4).symm
  have _transport := exercise_4_4_assumed hp.out hp_eq (a : ZMod p)
  have no_int_root : ∀ x : ℤ, ¬ IsPrimitiveRoot x p := by
    intro x hx
    rcases Int.isUnit_iff.mp (hx.isUnit hp.out.ne_zero) with rfl | rfl
    · exact hp.out.ne_one (Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by rw [one_pow])))
    · have hpow := hx.pow_eq_one
      rw [(hp.out.odd_of_ne_two hp_ne_two).neg_one_pow] at hpow
      have hbad : (0 : ℤ) < -1 := by
        rw [hpow]
        exact Int.zero_lt_one
      exact (not_lt_of_ge (Int.negSucc_le_zero 0)) hbad
  constructor
  · intro h
    exact (no_int_root (-a) h).elim -- non-rewrite step
  · intro h
    exact (no_int_root a h).elim -- non-rewrite step
