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
  constructor
  · intro h h4
    subst n
    norm_num at h
  · intro h4
    by_cases h1 : (n : ℕ) = 1
    · simpa [h1]
    have hn1 : 1 < (n : ℕ) := by
      have hnpos : 0 < (n : ℕ) := n.property
      omega
    obtain ⟨m, hm_dvd, hm2, hm_lt⟩ := Nat.exists_dvd_of_not_prime2 hn1 hn0
    have hm_pos : 0 < m := by omega
    obtain ⟨q, hmq'⟩ := hm_dvd
    have hmq : m * q = (n : ℕ) := hmq'.symm
    have hq2 : 2 ≤ q := by
      have hq0 : q ≠ 0 := by
        intro hq
        rw [hq, mul_zero] at hmq
        have hnpos : 0 < (n : ℕ) := n.property
        omega
      have hq1 : q ≠ 1 := by
        intro hq
        rw [hq, mul_one] at hmq
        omega
      omega
    have hsum : m + q ≤ (n : ℕ) - 1 := by
      have hn4 : (n : ℕ) ≠ 4 := by exact_mod_cast h4
      have hor : 3 ≤ m ∨ 3 ≤ q := by
        by_contra h
        push_neg at h
        have : m = 2 ∧ q = 2 := by omega
        rcases this with ⟨hm_eq, hq_eq⟩
        rw [hm_eq, hq_eq] at hmq
        norm_num at hmq
        exact hn4 hmq.symm
      have hlt : m + q < m * q := by
        rcases hor with hm3 | hq3
        · have hp : 0 ≤ ((m : ℤ) - 3) * ((q : ℤ) - 1) :=
            mul_nonneg (by omega) (by omega)
          exact_mod_cast (show (m : ℤ) + q < m * q by nlinarith)
        · have hp : 0 ≤ ((m : ℤ) - 1) * ((q : ℤ) - 3) :=
            mul_nonneg (by omega) (by omega)
          exact_mod_cast (show (m : ℤ) + q < m * q by nlinarith)
      rw [hmq] at hlt
      omega
    have hsum' : m + q ≤ m * q - 1 := by
      simpa only [hmq] using hsum
    apply Nat.modEq_zero_iff_dvd.2
    rw [← hmq]
    exact (Nat.mul_dvd_mul (Nat.dvd_factorial hm_pos (by omega))
      (Nat.dvd_factorial (by omega) (by omega))).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add m q |>.trans
        (Nat.factorial_dvd_factorial hsum'))
