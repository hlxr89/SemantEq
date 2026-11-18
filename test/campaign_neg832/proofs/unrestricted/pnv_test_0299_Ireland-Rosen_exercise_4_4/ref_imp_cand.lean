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
theorem dummy (p : ℕ) [Fact (Nat.Prime p)] (hp : (p : ℤ) = 4*t+1) (a : ℤ) (hap : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := by
  have hpNat : Nat.Prime p := Fact.out
  have hpne : p ≠ 0 := hpNat.ne_zero
  have haunit : IsUnit a := hap.isUnit hpne
  rcases (Int.isUnit_iff.mp haunit) with rfl | rfl
  · exact ((hap.ne_one hpNat.one_lt) rfl).elim
  · have hpodd : Odd p := by
      have ht : 0 ≤ t := by omega
      refine ⟨2 * t.toNat, ?_⟩
      rw [← Int.ofNat_inj]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.toNat_of_nonneg ht]
      omega
    have hpow : (-1 : ℤ) ^ p = 1 := hap.pow_eq_one
    rw [hpodd.neg_one_pow] at hpow
    norm_num at hpow
