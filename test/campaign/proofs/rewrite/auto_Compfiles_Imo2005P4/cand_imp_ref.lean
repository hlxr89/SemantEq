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
  have hseq (n : ℕ) :
      Int.natAbs ((2 : ℤ) ^ n + 3 ^ n + 6 ^ n - 1) =
        2 ^ n + 3 ^ n + 6 ^ n - 1 := by
    have hsum : 1 ≤ 2 ^ n + 3 ^ n + 6 ^ n :=
      le_trans (Nat.one_le_pow' n 1)
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
      (Int.natAbs_natCast_sub_natCast_of_ge hsum)
  constructor
  · intro href_left
    have hc_left :
        ∀ n : ℕ, 1 ≤ n → Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1) := by
      intro n hn
      have href_n := href_left n hn
      rw [a, Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, hseq,
        Nat.coprime_comm] at href_n
      exact href_n
    have hc_right := (Imo2005P4_assumed k hk).mp hc_left
    have hk_one : k = 1 := by
      simpa only [Imo2005P4_solution, Set.mem_singleton_iff] using hc_right
    rw [SolutionSet, Set.mem_singleton_iff]
    apply Subtype.ext
    exact hk_one
  · intro href_right
    have hk_one : k = 1 := by
      rw [SolutionSet, Set.mem_singleton_iff] at href_right
      exact congrArg Subtype.val href_right
    have hc_right : k ∈ Imo2005P4_solution := by
      simpa only [Imo2005P4_solution, Set.mem_singleton_iff] using hk_one
    have hc_left := (Imo2005P4_assumed k hk).mpr hc_right
    intro n hn
    rw [a, Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, hseq,
      Nat.coprime_comm]
    exact hc_left n hn
