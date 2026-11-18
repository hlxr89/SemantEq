import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_assumed {p n : ℕ} (hp : p.Prime) (hpn : p = 2^n + 1) :
  IsPrimitiveRoot (3 : ZMod p) p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℕ} (n : ℕ) (hp : p = 2^n + 1) (hfp : Nat.Prime p) : IsPrimitiveRoot 3 p := by
  exfalso
  letI : Fact (Nat.Prime p) := ⟨hfp⟩
  have hroot := exercise_4_6_assumed hfp hp
  by_cases h3 : (3 : ZMod p) = 0
  · exact hroot.ne_zero hfp.ne_zero h3
  · have hdvd : p ∣ p - 1 :=
      hroot.dvd_of_pow_eq_one (p - 1) (ZMod.pow_card_sub_one_eq_one h3)
    have hp2 : 2 ≤ p := hfp.two_le
    have hpos : 0 < p - 1 := by omega
    have hle : p ≤ p - 1 := Nat.le_of_dvd hpos hdvd
    omega
