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
  obtain ⟨k, hk⟩ := erdos_10_assumed
  rw [eventually_atTop] at hk
  obtain ⟨N, hN⟩ := hk
  refine ⟨max k N, Set.ext fun n => ?_⟩
  constructor
  · rintro ⟨p, pows, hp, hpows, rfl⟩
    simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    have hp2 : 2 ≤ p := hp.two_le
    omega
  · intro hn
    simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hn
    have hn2 : 2 ≤ n := by omega
    by_cases hlarge : N ≤ n
    · obtain ⟨p, pows, hp, hpows, heq⟩ := hN n hlarge
      exact ⟨p, pows, hp, hpows.trans (le_max_left k N), heq⟩
    · refine ⟨2, Multiset.replicate (n - 2) 0, Nat.prime_two, ?_, ?_⟩
      · simp only [Multiset.card_replicate]
        exact (Nat.sub_le n 2).trans ((Nat.lt_of_not_ge hlarge).le.trans (le_max_right k N))
      · simp [hn2]

end Erdos10
