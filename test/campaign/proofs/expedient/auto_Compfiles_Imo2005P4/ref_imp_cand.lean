import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def a (n : ℕ) : ℤ := 2 ^ n + 3 ^ n + 6 ^ n - 1

def SolutionSet : Set ℕ+ := { 1 }

/-- The set of positive integers relatively prime to every term of the sequence:
only 1. -/
def Imo2005P4_solution : Set ℕ := {1}

-- ===== assumed statement (antecedent) =====
theorem Imo2005P4_refs_assumed {k : ℕ} (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n → IsCoprime (a n) k) ↔ ⟨k, hk⟩ ∈ SolutionSet := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo2005P4 (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n → Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1)) ↔
      k ∈ Imo2005P4_solution := by
  constructor
  · intro h
    have h' : ∀ n : ℕ, 1 ≤ n → IsCoprime (a n) k := by
      intro n hn
      rw [Int.isCoprime_iff_nat_coprime]
      rw [show (a n).natAbs = 2 ^ n + 3 ^ n + 6 ^ n - 1 by
        have hp : 1 ≤ (2 ^ n + 3 ^ n + 6 ^ n : ℕ) := by
          exact (by positivity : 0 < (2 ^ n + 3 ^ n + 6 ^ n : ℕ))
        have ha : a n = ((2 ^ n + 3 ^ n + 6 ^ n - 1 : ℕ) : ℤ) := by
          rw [a, Nat.cast_sub hp]
          norm_num
        rw [ha]
        exact Int.natAbs_natCast _]
      exact (h n hn).symm
    have hp := (Imo2005P4_refs_assumed hk).mp h'
    simp only [SolutionSet, Set.mem_singleton_iff] at hp
    have hk1 : k = 1 := by
      simpa using congrArg Subtype.val hp
    simpa [Imo2005P4_solution] using hk1
  · intro h
    simp only [Imo2005P4_solution, Set.mem_singleton_iff] at h
    subst k
    simp
