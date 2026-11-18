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
  have no_root : ∀ x : ℤ, ¬ IsPrimitiveRoot x p := by
    intro x hx
    have hxunit : IsUnit x := hx.isUnit hp.out.ne_zero
    rw [Int.isUnit_iff] at hxunit
    rcases hxunit with rfl | rfl
    · have : p = 1 := Nat.dvd_one.mp (hx.dvd_of_pow_eq_one 1 (by simp))
      exact hp.out.ne_one this
    · have hpne2 : p ≠ 2 := by
        intro h
        subst p
        have hbad := hp1.out
        norm_num at hbad
      have hpdiv : p ∣ 2 := hx.dvd_of_pow_eq_one 2 (by norm_num)
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hpone | hptwo
      · exact hp.out.ne_one hpone
      · exact hpne2 hptwo
  simp only [no_root]
