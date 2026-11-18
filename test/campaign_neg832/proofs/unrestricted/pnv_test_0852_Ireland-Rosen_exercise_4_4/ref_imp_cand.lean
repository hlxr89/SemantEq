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
theorem dummy {p : ℕ} [hp : Fact (Nat.Prime p)] (hp1 : p % 4 = 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have no_int_root (x : ℤ) (h : IsPrimitiveRoot x p) : False := by
    have hu := h.isUnit hp.out.ne_zero
    have hsquare : x ^ 2 = 1 := by
      rcases Int.isUnit_iff.mp hu with ha | ha
      · rw [ha]
        norm_num
      · rw [ha]
        norm_num
    have hdvd : p ∣ 2 := h.dvd_of_pow_eq_one 2 hsquare
    rcases (Nat.dvd_prime (show Nat.Prime 2 by norm_num)).mp hdvd with hp_one | hp_two
    · exact (hp.out.ne_one hp_one).elim
    · subst p
      norm_num at hp1
  constructor
  · intro h
    exact (no_int_root a h).elim
  · intro h
    exact (no_int_root (-a) h).elim
