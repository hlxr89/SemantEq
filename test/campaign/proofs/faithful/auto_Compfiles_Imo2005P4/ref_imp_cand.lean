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
  rw [← show (⟨k, hk⟩ : ℕ+) ∈ SolutionSet ↔ k ∈ Imo2005P4_solution by
    change (⟨k, hk⟩ : ℕ+) = (1 : ℕ+) ↔ k = 1
    exact Subtype.ext_iff]
  rw [← Imo2005P4_refs_assumed hk]
  constructor
  · intro h n hn
    have hpos : 1 ≤ 2 ^ n + 3 ^ n + 6 ^ n := by
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      exact Nat.le_add_right_of_le (Nat.le_add_right_of_le hpow)
    have hcast : ((2 ^ n + 3 ^ n + 6 ^ n - 1 : ℕ) : ℤ) = a n := by
      rw [Nat.cast_sub hpos]
      norm_num [a]
    have hc : Nat.Coprime (2 ^ n + 3 ^ n + 6 ^ n - 1) k := (h n hn).symm
    have hi := hc.isCoprime
    simpa only [hcast] using hi
  · intro h n hn
    have hpos : 1 ≤ 2 ^ n + 3 ^ n + 6 ^ n := by
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      exact Nat.le_add_right_of_le (Nat.le_add_right_of_le hpow)
    have hcast : ((2 ^ n + 3 ^ n + 6 ^ n - 1 : ℕ) : ℤ) = a n := by
      rw [Nat.cast_sub hpos]
      norm_num [a]
    have hi : IsCoprime ((2 ^ n + 3 ^ n + 6 ^ n - 1 : ℕ) : ℤ) (k : ℤ) := by
      simpa only [hcast] using h n hn
    exact hi.natCoprime.symm
