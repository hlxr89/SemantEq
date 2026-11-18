import Mathlib

open ArithmeticFunction.sigma

namespace Erdos412

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem erdos_412_assumed (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ i j, σ i m = σ j n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_412 :
    ∀ᵉ (m ≥ 2) (n ≥ 2), ∃ i j, (σ 1)^[i] m = (σ 1)^[j] n := by
  exfalso
  obtain ⟨i, j, hij⟩ := erdos_412_assumed 3 4 (by omega) (by omega)
  have hi : σ i 3 = 1 + 3 ^ i := by
    rw [show 3 = 3 ^ 1 by norm_num, ArithmeticFunction.sigma_apply_prime_pow (by norm_num)]
    simp [Finset.sum_range_succ]
  have hj : σ j 4 = 1 + 2 ^ j + (2 ^ j) ^ 2 := by
    rw [show 4 = 2 ^ 2 by norm_num, ArithmeticFunction.sigma_apply_prime_pow (by norm_num)]
    simp [Finset.sum_range_succ, pow_mul]
    calc
      4 ^ j = (2 ^ 2) ^ j := by norm_num
      _ = 2 ^ (2 * j) := by rw [pow_mul]
      _ = 2 ^ (j * 2) := by rw [Nat.mul_comm]
      _ = (2 ^ j) ^ 2 := by rw [pow_mul]
  rw [hi, hj] at hij
  cases i with
  | zero =>
      have h2 : 0 < 2 ^ j := pow_pos (by omega) _
      have h4 : 0 < 4 ^ j := pow_pos (by omega) _
      have hs : 0 < (2 ^ j) ^ 2 := pow_pos h2 _
      norm_num at hij
      omega
  | succ i =>
      cases j with
      | zero =>
          have h3 : 0 < 3 ^ i := pow_pos (by omega) _
          norm_num [pow_succ] at hij
          omega
      | succ j =>
          have hodd : Odd (3 ^ (i + 1)) := (by norm_num : Odd 3).pow
          have heven : Even (2 ^ (j + 1)) := by
            rw [pow_succ]
            exact Even.mul_left (by norm_num : Even 2) _
          have heven_sq : Even ((2 ^ (j + 1)) ^ 2) := by
            simpa [pow_two] using heven.mul_right (2 ^ (j + 1))
          obtain ⟨a, ha⟩ := hodd
          obtain ⟨b, hb⟩ := heven
          obtain ⟨c, hc⟩ := heven_sq
          omega

end Erdos412
