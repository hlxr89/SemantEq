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
: ∀ n, n ≥ 1 → (∃ k : ℤ, a n = k * n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1999_a6 (a : ℕ → ℚ)
    (ha1 : a 1 = 1) (ha2 : a 2 = 2) (ha3 : a 3 = 24)
    (ha : ∀ n : ℕ, 4 ≤ n →
      a n = (6 * (a (n - 1)) ^ 2 * a (n - 3) - 8 * a (n - 1) * (a (n - 2)) ^ 2) /
        (a (n - 2) * a (n - 3))) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, a n = (n : ℚ) * k := by
  let b : ℤ → ℝ := fun z => if 0 ≤ z then (a z.toNat : ℝ) else 0
  have hb (n : ℕ) : b n = (a n : ℝ) := by simp [b]
  have H := putnam_1999_a6_refs_assumed b
    (by simpa [hb] using congrArg ((↑) : ℚ → ℝ) ha1)
    (by simpa [hb] using congrArg ((↑) : ℚ → ℝ) ha2)
    (by simpa [hb] using congrArg ((↑) : ℚ → ℝ) ha3)
    (by
      intro n hn
      have h1 : ((n : ℤ) - 1).toNat = n - 1 := by omega
      have h2 : ((n : ℤ) - 2).toNat = n - 2 := by omega
      have h3 : ((n : ℤ) - 3).toNat = n - 3 := by omega
      simpa [b, show (0 : ℤ) ≤ (n : ℤ) - 1 by omega,
        show (0 : ℤ) ≤ (n : ℤ) - 2 by omega,
        show (0 : ℤ) ≤ (n : ℤ) - 3 by omega, h1, h2, h3,
        show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega] using
        congrArg ((↑) : ℚ → ℝ) (ha n hn))
  intro n hn
  obtain ⟨k, hk⟩ := H (n : ℤ) (by exact_mod_cast hn)
  refine ⟨k, ?_⟩
  simp [b] at hk
  norm_cast at hk ⊢
  simpa [mul_comm] using hk
