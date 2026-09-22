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
  constructor
  · intro h
    have h' : ∀ n : ℕ, 1 ≤ n → Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1) := by
      intro n hn
      have hc := (Int.isCoprime_iff_nat_coprime.mp (h n hn)).symm
      rw [show (a n).natAbs = 2 ^ n + 3 ^ n + 6 ^ n - 1 by
        have hp : 1 ≤ (2 ^ n + 3 ^ n + 6 ^ n : ℕ) := by
          exact (by positivity : 0 < (2 ^ n + 3 ^ n + 6 ^ n : ℕ))
        have ha : a n = ((2 ^ n + 3 ^ n + 6 ^ n - 1 : ℕ) : ℤ) := by
          rw [a, Nat.cast_sub hp]
          norm_num
        rw [ha]
        exact Int.natAbs_natCast _] at hc
      exact hc
    have hk1 : k = 1 := by
      simpa [Imo2005P4_solution] using (Imo2005P4_assumed k hk).mp h'
    subst k
    simp [SolutionSet]
  · intro h
    have hp : (⟨k, hk⟩ : ℕ+) = 1 := by simpa [SolutionSet] using h
    have hk1 : k = 1 := by simpa using congrArg Subtype.val hp
    subst k
    intro n hn
    exact isCoprime_one_right
