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
theorem dummy {p : ℕ} (hp : p.Prime) (h : ∃ t, p = 4 * t + 1) (a : ℤ) : IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  have not_primitive (x : ℤ) : ¬ IsPrimitiveRoot x p := by
    intro hx
    rcases Int.isUnit_iff.mp (hx.isUnit hp.ne_zero) with rfl | rfl
    · exact hx.ne_one hp.one_lt rfl
    · have hd : p ∣ 2 := hx.dvd_of_pow_eq_one 2 (by norm_num)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp_one | hp_two
      · exact hp.ne_one hp_one
      · obtain ⟨t, ht⟩ := h
        omega
  exact iff_of_false (not_primitive a) (not_primitive (-a))
