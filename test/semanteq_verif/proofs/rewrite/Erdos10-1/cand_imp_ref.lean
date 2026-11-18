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
  rw [eventually_atTop]
  refine ⟨2, ?_⟩
  intro n hn
  rw [hk]
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  exact (Nat.two_le_iff n).mp hn

end Erdos10
