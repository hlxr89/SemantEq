import Mathlib

open scoped Nat

-- ===== unified context (both sides' local defs, merged) =====
def solution_set : Set (ℕ × ℕ) := { (1,1), (2,3) }

/-- The pairs (n, k) of positive integers solving the equation: (1, 1) and (2, 3). -/
def Imo2019P4_solution : Set (ℕ × ℕ) := {(1, 1), (2, 3)}

-- ===== assumed statement (antecedent) =====
theorem Imo2019P4_assumed (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.factorial k = ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) ↔
      (n, k) ∈ Imo2019P4_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo2019P4_refs (n k : ℕ) :
    (n, k) ∈ solution_set ↔
    0 < n ∧ 0 < k ∧
    (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2:ℤ)^n - (2:ℤ)^i) := by
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
  constructor
  · intro hmem
    have hmem' : (n, k) ∈ Imo2019P4_solution := by
      exact hmem
    have hcases : (n = 1 ∧ k = 1) ∨ n = 2 ∧ k = 3 := by
      simpa only [Imo2019P4_solution, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] using hmem'
    rcases hcases with hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      refine ⟨Nat.zero_lt_succ 0, Nat.zero_lt_succ 0, ?_⟩
      exact hcast.mp ((Imo2019P4_assumed 1 1 (Nat.zero_lt_succ 0)
        (Nat.zero_lt_succ 0)).mpr hmem')
    · rcases hcase with ⟨rfl, rfl⟩
      refine ⟨Nat.zero_lt_succ 1, Nat.zero_lt_succ 2, ?_⟩
      exact hcast.mp ((Imo2019P4_assumed 2 3 (Nat.zero_lt_succ 1)
        (Nat.zero_lt_succ 2)).mpr hmem')
  · rintro ⟨hn, hk, hz⟩
    have hnat := hcast.mpr hz
    have hmem := (Imo2019P4_assumed n k hn hk).mp hnat
    exact hmem
