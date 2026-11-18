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
  obtain ⟨a, ha⟩ := hk
  refine ⟨k + a, Set.ext ?_⟩
  intro n
  constructor
  · intro hn
    obtain ⟨p, pows, hp, hpows, rfl⟩ := hn
    simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    have htotal : 2 ≤ p + (pows.map (2 ^ ·)).sum :=
      le_trans (Nat.Prime.two_le hp) (Nat.le_add_right p _)
    constructor
    · exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two htotal)
    · exact Nat.ne_of_gt (lt_of_lt_of_le Nat.one_lt_two htotal)
  · intro hn
    simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hn
    by_cases hna : a ≤ n
    · obtain ⟨p, pows, hp, hpows, heq⟩ := ha n hna
      exact ⟨p, pows, hp, le_trans hpows (Nat.le_add_right k a), heq⟩
    · have hn2 : 2 ≤ n := (Nat.two_le_iff n).mpr hn
      refine ⟨2, Multiset.replicate (n - 2) 0, Nat.prime_two, ?_, ?_⟩
      · rw [Multiset.card_replicate]
        exact le_trans (Nat.sub_le n 2)
          (le_trans (Nat.le_of_lt (Nat.lt_of_not_ge hna)) (Nat.le_add_left a k))
      · simp only [Multiset.map_replicate, pow_zero, Multiset.sum_replicate,
          nsmul_eq_mul, mul_one]
        exact Nat.add_sub_of_le hn2

end Erdos10
