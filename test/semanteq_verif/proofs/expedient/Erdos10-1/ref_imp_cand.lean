import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos10

abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

-- ===== assumed statement (antecedent) =====
theorem erdos_10_assumed : ∃ k, ∀ᶠ n : ℕ in atTop, n ∈ sumPrimeAndTwoPows k := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_10_goal : ∃ k, sumPrimeAndTwoPows k = Set.univ \ {0, 1} := by
  rcases erdos_10_assumed with ⟨k, hk⟩
  rw [eventually_atTop] at hk
  rcases hk with ⟨N, hN⟩
  refine ⟨max k N, Set.ext fun n => ?_⟩
  constructor
  · rintro ⟨p, pows, hp, hpows, rfl⟩
    have hp2 := hp.two_le
    simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  · simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    intro hn
    by_cases hnN : N ≤ n
    · rcases hN n hnN with ⟨p, pows, hp, hpows, rfl⟩
      exact ⟨p, pows, hp, hpows.trans (Nat.le_max_left _ _), rfl⟩
    · have hn2 : 2 ≤ n := by omega
      refine ⟨2, Multiset.replicate (n - 2) 0, Nat.prime_two, ?_, ?_⟩
      · simp
        omega
      · simp
        omega

end Erdos10
