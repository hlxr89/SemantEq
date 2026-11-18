import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (h : n ≠ 0) (h' : ¬ Prime n) : (Nat.factorial n % n) = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_10 {n : ℕ+} (hn0 : ¬ n.Prime) :
  Nat.factorial (n-1) ≡ 0 [MOD n] ↔ n ≠ 4 := by
  rw [Nat.modEq_zero_iff_dvd]
  constructor
  · intro hfac h4
    subst n
    norm_num at hfac
  · intro h4
    by_cases hn1 : (n : ℕ) = 1
    · have hn1' : n = 1 := Subtype.ext hn1
      subst n
      norm_num
    have hn2 : 2 ≤ (n : ℕ) := by
      have hnpos : 0 < (n : ℕ) := n.prop
      omega
    obtain ⟨m, hm, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 hn2 hn0
    obtain ⟨k, hk⟩ := hm
    have hmk_ne : m * k ≠ 4 := by
      intro hmk
      apply h4
      apply Subtype.ext
      simpa using hk.trans hmk
    rw [hk] at hmn ⊢
    have hk2 : 2 ≤ k := by
      nlinarith
    have hsum : m + k ≤ m * k - 1 := by
      by_cases hm_eq : m = 2
      · subst m
        have hk3 : 3 ≤ k := by omega
        omega
      · have hm3 : 3 ≤ m := by omega
        have hm_nonneg : 0 ≤ (m : ℤ) - 3 := by omega
        have hk_nonneg : 0 ≤ (k : ℤ) - 2 := by omega
        have hltZ : (m : ℤ) + (k : ℤ) < (m : ℤ) * (k : ℤ) := by
          nlinarith [mul_nonneg hm_nonneg hk_nonneg]
        have hlt : m + k < m * k := by exact_mod_cast hltZ
        omega
    have hmfac : m ∣ m.factorial := Nat.dvd_factorial (by omega) (le_refl m)
    have hkfac : k ∣ k.factorial := Nat.dvd_factorial (by omega) (le_refl k)
    exact (Nat.mul_dvd_mul hmfac hkfac).trans
      ((Nat.factorial_mul_factorial_dvd_factorial_add m k).trans
        (Nat.factorial_dvd_factorial hsum))
