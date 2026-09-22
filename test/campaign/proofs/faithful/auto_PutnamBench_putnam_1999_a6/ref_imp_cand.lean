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
  let ar : ℤ → ℝ := fun z => if 0 ≤ z then (a z.toNat : ℝ) else 0
  have har (n : ℕ) : ar n = (a n : ℝ) := by simp [ar]
  have hdiv := putnam_1999_a6_refs_assumed ar
    (by simpa [har] using congrArg ((↑) : ℚ → ℝ) ha1)
    (by simpa [har] using congrArg ((↑) : ℚ → ℝ) ha2)
    (by simpa [har] using congrArg ((↑) : ℚ → ℝ) ha3)
    (by
      intro n hn
      have hs1 : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      have hs2 : (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) := by omega
      have hs3 : (n : ℤ) - 3 = ((n - 3 : ℕ) : ℤ) := by omega
      rw [har, hs1, hs2, hs3, har, har, har]
      exact_mod_cast ha n hn)
  intro n hn
  obtain ⟨k, hk⟩ := hdiv n (by exact_mod_cast hn)
  refine ⟨k, ?_⟩
  rw [har] at hk
  have : a n = (k : ℚ) * n := by exact_mod_cast hk
  simpa [mul_comm] using this
