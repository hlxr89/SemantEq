import Mathlib

open scoped Nat

-- ===== unified context (both sides' local defs, merged) =====
def solution_set : Set (ℕ × ℕ) := { (1,1), (2,3) }

/-- The pairs (n, k) of positive integers solving the equation: (1, 1) and (2, 3). -/
def Imo2019P4_solution : Set (ℕ × ℕ) := {(1, 1), (2, 3)}

-- ===== assumed statement (antecedent) =====
theorem Imo2019P4_refs_assumed (n k : ℕ) :
    (n, k) ∈ solution_set ↔
    0 < n ∧ 0 < k ∧
    (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2:ℤ)^n - (2:ℤ)^i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo2019P4 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.factorial k = ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) ↔
      (n, k) ∈ Imo2019P4_solution := by
  have hfactor (i : ℕ) (hi : i ∈ Finset.range n) :
      ((2 ^ n - 2 ^ i : ℕ) : ℤ) = (2 : ℤ) ^ n - (2 : ℤ) ^ i := by
    rw [Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_ofNat]
    · exact Nat.pow_le_pow_right (Nat.zero_lt_succ 1)
        (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hprod :
      ((∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) : ℕ) : ℤ) =
        ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl hfactor
  have hcast :
      Nat.factorial k = ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) ↔
        (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) := by
    rw [← Nat.cast_inj (R := ℤ), hprod]
  rw [show (n, k) ∈ Imo2019P4_solution ↔ (n, k) ∈ solution_set by rfl]
  rw [Imo2019P4_refs_assumed n k]
  simp only [hn, hk, true_and]
  exact hcast
