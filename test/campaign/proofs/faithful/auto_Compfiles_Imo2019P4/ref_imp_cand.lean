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
  have hsets : solution_set = Imo2019P4_solution := rfl
  have hprod :
      ((↑(∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)) : ℕ) : ℤ) =
        ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) := by
    simp only [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub]
    · norm_num
    · exact Nat.pow_le_pow_right (by omega) (Finset.mem_range.mp hi).le
  constructor
  · intro h
    rw [← hsets]
    apply (Imo2019P4_refs_assumed n k).2
    refine ⟨hn, hk, ?_⟩
    rw [← hprod, ← h]
  · intro h
    rw [← hsets] at h
    have hint := (Imo2019P4_refs_assumed n k).1 h
    apply_mod_cast hint.2.2.trans hprod.symm
