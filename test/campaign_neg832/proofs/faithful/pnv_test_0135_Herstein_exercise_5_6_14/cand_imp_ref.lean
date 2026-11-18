import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : (∃ (x : F), x ^ (p ^ n) = x) → (∀ x y : F, x ≠ y → x ^ (p ^ n) ≠ y ^ (p ^ n)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  letI : Fact (Nat.Prime p) := ⟨CharP.char_prime_of_ne_zero F hp⟩
  have hpn : p ^ n ≠ 0 := pow_ne_zero n hp
  have hinj := dummy_assumed (F := F) p n ⟨0, zero_pow hpn⟩
  have hneg : (-1 : F) ≠ 0 := by
    have hpow := hinj 0 1 zero_ne_one
    simpa using hpow
  have hdiv : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
  have hcast : ((p ^ n : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F p (p ^ n)).2 hdiv
  subst m
  simpa [isUnit_iff_ne_zero] using
    (separable_C_mul_X_pow_add_C_mul_X_add_C (R := F) 1 (-1) 0 hcast
      (isUnit_iff_ne_zero.mpr hneg))
