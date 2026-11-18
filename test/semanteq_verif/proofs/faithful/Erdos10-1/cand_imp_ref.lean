import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos10

abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

-- ===== assumed statement (antecedent) =====
theorem erdos_10_assumed : ∃ k, sumPrimeAndTwoPows k = Set.univ \ {0, 1} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_10_goal : ∃ k, ∀ᶠ n : ℕ in atTop, n ∈ sumPrimeAndTwoPows k := by
  obtain ⟨k, hk⟩ := erdos_10_assumed
  refine ⟨k, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  apply (Set.ext_iff.mp hk n).mpr
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  omega

end Erdos10
