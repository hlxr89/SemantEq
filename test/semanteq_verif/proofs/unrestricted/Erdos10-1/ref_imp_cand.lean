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
  rcases (eventually_atTop.1 hk) with ⟨N, hN⟩
  refine ⟨max k N, Set.ext ?_⟩
  intro n
  constructor
  · intro hn
    rcases hn with ⟨p, pows, hp, hpows, rfl⟩
    have hp2 : 2 ≤ p := Nat.Prime.two_le hp
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_and]
    omega
  · intro hn
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_and] at hn
    have hn2 : 2 ≤ n := by omega
    by_cases htail : N ≤ n
    · rcases hN n htail with ⟨p, pows, hp, hpows, heq⟩
      exact ⟨p, pows, hp, hpows.trans (Nat.le_max_left _ _), heq⟩
    · refine ⟨2, Multiset.replicate (n - 2) 0, Nat.prime_two, ?_, ?_⟩
      · simp only [Multiset.card_replicate]
        omega
      · simp [Nat.add_sub_of_le hn2]

end Erdos10
