import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def a (n : ℕ) : ℤ := 2 ^ n + 3 ^ n + 6 ^ n - 1

def SolutionSet : Set ℕ+ := { 1 }

/-- The set of positive integers relatively prime to every term of the sequence:
only 1. -/
def Imo2005P4_solution : Set ℕ := {1}

-- ===== assumed statement (antecedent) =====
theorem Imo2005P4_assumed (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n → Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1)) ↔
      k ∈ Imo2005P4_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo2005P4_refs {k : ℕ} (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n → IsCoprime (a n) k) ↔ ⟨k, hk⟩ ∈ SolutionSet := by
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
  rw [SolutionSet, Set.mem_singleton_iff]
  constructor
  · intro h
    have hcand : ∀ n : ℕ, 1 ≤ n → Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1) := by
      intro n hn
      exact (hbridge n hn).1 (h n hn)
    have hs := (Imo2005P4_assumed k hk).1 hcand
    have hk1 : k = 1 := by simpa [Imo2005P4_solution] using hs
    exact Subtype.ext hk1
  · intro h
    have hk1 : k = 1 := congrArg Subtype.val h
    subst k
    intro n hn
    exact isCoprime_one_right
