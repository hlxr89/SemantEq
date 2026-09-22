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
  have hbridge (n : ℕ) (hn : 1 ≤ n) :
      IsCoprime (a n) k ↔ Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1) := by
    rw [a, Int.isCoprime_iff_nat_coprime]
    rw [Int.natAbs_natCast]
    rw [Nat.coprime_comm]
    have htwo : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hthree : (0 : ℤ) ≤ 3 ^ n := by positivity
    have hsix : (0 : ℤ) ≤ 6 ^ n := by positivity
    have hpos : (0 : ℤ) ≤ 2 ^ n + 3 ^ n + 6 ^ n - 1 := by omega
    have heq : (2 ^ n + 3 ^ n + 6 ^ n - 1 : ℤ).natAbs =
        (2 ^ n + 3 ^ n + 6 ^ n - 1 : ℕ) := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.natAbs_of_nonneg hpos]
      have htwoNat : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow n 2 (by norm_num)
      have hsumNat : 1 ≤ (2 : ℕ) ^ n + 3 ^ n + 6 ^ n := by
        calc
          1 ≤ (2 : ℕ) ^ n := htwoNat
          _ ≤ 2 ^ n + 3 ^ n := Nat.le_add_right _ _
          _ ≤ 2 ^ n + 3 ^ n + 6 ^ n := Nat.le_add_right _ _
      rw [Nat.cast_sub hsumNat]
      norm_num
    rw [heq]
  rw [Imo2005P4_solution, Set.mem_singleton_iff]
  constructor
  · intro h
    have href : ∀ n : ℕ, 1 ≤ n → IsCoprime (a n) k := by
      intro n hn
      exact (hbridge n hn).2 (h n hn)
    have hs := (Imo2005P4_refs_assumed hk).1 href
    simpa [SolutionSet] using congrArg Subtype.val hs
  · intro h
    subst k
    intro n hn
    exact Nat.coprime_one_left _
