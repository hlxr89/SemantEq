import Mathlib

open ArithmeticFunction.sigma

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos412

-- ===== assumed statement (antecedent) =====
theorem erdos_412_assumed (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ i j, σ i m = σ j n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_412_goal :
    ∀ᵉ (m ≥ 2) (n ≥ 2), ∃ i j, (σ 1)^[i] m = (σ 1)^[j] n := by
  exfalso
  obtain ⟨i, j, hij⟩ := erdos_412_assumed 2 6 (by norm_num) (by norm_num)
  have h2 (k : ℕ) : σ k 2 = 2 ^ k + 1 := by
    rw [ArithmeticFunction.sigma_apply]
    norm_num
  have h6 (k : ℕ) : σ k 6 = (2 ^ k + 1) * (3 ^ k + 1) := by
    rw [ArithmeticFunction.sigma_apply]
    have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by native_decide
    rw [hdiv]
    simp
    rw [show 6 ^ k = 2 ^ k * 3 ^ k by rw [← Nat.mul_pow]]
    ring
  rw [h2, h6] at hij
  cases i with
  | zero =>
      simp at hij
      have h2p : 0 < 2 ^ j := pow_pos (by omega) _
      have h3p : 0 < 3 ^ j := pow_pos (by omega) _
      nlinarith
  | succ i =>
      have hevenpow : Even (2 ^ (i + 1)) := by
        rw [pow_succ]
        exact even_two.mul_left _
      have hoddleft : Odd (2 ^ (i + 1) + 1) := hevenpow.add_odd odd_one
      have hodd3 : Odd (3 ^ j) := (show Odd (3 : ℕ) by norm_num).pow
      have hevenright : Even ((2 ^ j + 1) * (3 ^ j + 1)) :=
        (hodd3.add_odd odd_one).mul_left _
      rw [hij] at hoddleft
      rcases hoddleft with ⟨a, ha⟩
      rcases hevenright with ⟨b, hb⟩
      omega

end Erdos412
