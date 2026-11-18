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
  have hpn : Nat.Prime p := (Fact.out : Prime p).nat_prime
  constructor <;> intro h
  · exfalso
    have hs : ((-a) : ℤ) ^ 2 = 1 := Int.isUnit_sq (h.isUnit hpn.ne_zero)
    have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (h.dvd_of_pow_eq_one 2 hs)).resolve_left hpn.ne_one
    omega
  · exfalso
    have hs : a ^ 2 = 1 := Int.isUnit_sq (h.isUnit hpn.ne_zero)
    have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (h.dvd_of_pow_eq_one 2 hs)).resolve_left hpn.ne_one
    omega
