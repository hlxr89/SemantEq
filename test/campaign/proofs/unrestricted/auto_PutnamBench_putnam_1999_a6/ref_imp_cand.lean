import Mathlib

open Filter Topology Metric

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1999_a6_refs_assumed
(a : ℤ → ℝ)
(ha1 : a 1 = 1)
(ha2 : a 2 = 2)
(ha3 : a 3 = 24)
(hange4 : ∀ n : ℕ, n ≥ 4 → a n = (6 * (a (n - 1))^2 * (a (n - 3)) - 8 * (a (n - 1)) * (a (n - 2))^2)/(a (n - 2) * a (n - 3)))
: ∀ n, n ≥ 1 → (∃ k : ℤ, a n = k * n) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a6 (a : ℕ → ℚ)
    (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (ha : ∀ n : ℕ, 4 ≤ n →
      a n = (6 * (a (n - 1)) ^ 2 * a (n - 3) - 8 * a (n - 1) * (a (n - 2)) ^ 2) /
        (a (n - 2) * a (n - 3))) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, a n = (n : ℚ) * k := by
  let A : ℤ → ℝ := fun z => if 0 ≤ z then (a z.toNat : ℝ) else 0
  have hA1 : A 1 = 1 := by simp [A, ha1]
  have hA2 : A 2 = 2 := by simp [A, ha2]
  have hA3 : A 3 = 24 := by simp [A, ha3]
  have hA : ∀ n : ℕ, n ≥ 4 → A n =
      (6 * (A (n - 1))^2 * (A (n - 3)) - 8 * (A (n - 1)) * (A (n - 2))^2) /
        (A (n - 2) * A (n - 3)) := by
    intro n hn
    have hm1 : ((n : ℤ) - 1).toNat = n - 1 := by omega
    have hm2 : ((n : ℤ) - 2).toNat = n - 2 := by omega
    have hm3 : ((n : ℤ) - 3).toNat = n - 3 := by omega
    norm_num [A, hm1, hm2, hm3, ha n hn,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  intro n hn
  obtain ⟨k, hk⟩ := putnam_1999_a6_refs_assumed A hA1 hA2 hA3 hA (n : ℤ) (by omega)
  refine ⟨k, ?_⟩
  have hk' : (a n : ℝ) = (k : ℝ) * (n : ℝ) := by simpa [A] using hk
  have hkq : a n = (k : ℚ) * (n : ℚ) := by exact_mod_cast hk'
  simpa [mul_comm] using hkq
