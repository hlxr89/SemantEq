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
  have hp_nat : Nat.Prime p := hp.out.nat_prime
  have hp_form : p = 4 * (p / 4) + 1 := by omega
  have _href := exercise_4_4_assumed (p := p) (t := p / 4) hp_nat hp_form (a : ZMod p)
  have hp_pos : 0 < p := hp_nat.pos
  have not_primitive (x : ℤ) : ¬ IsPrimitiveRoot x p := by
    intro hx
    rcases (pow_eq_one_iff_of_ne_zero hp_pos.ne').mp hx.pow_eq_one with rfl | ⟨rfl, heven⟩
    · have hdvd : p ∣ 1 := hx.dvd_of_pow_eq_one 1 (by simp)
      exact hp_nat.ne_one (Nat.dvd_one.mp hdvd)
    · have hp_two : p = 2 := hp_nat.even_iff.mp heven
      norm_num [hp_two] at hp1
  exact ⟨fun h ↦ (not_primitive (-a) h).elim, fun h ↦ (not_primitive a h).elim⟩
