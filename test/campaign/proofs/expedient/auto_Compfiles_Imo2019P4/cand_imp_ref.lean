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
  have hprod :
      ((↑(∏ i ∈ Finset.range n, ((2 : ℕ) ^ n - (2 : ℕ) ^ i)) : ℤ)) =
        ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub]
    · norm_num
    · exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Finset.mem_range.mp hi))
  change (n, k) ∈ Imo2019P4_solution ↔ _
  constructor
  · intro h
    have hpos : 0 < n ∧ 0 < k := by
      simp only [Imo2019P4_solution, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] at h
      rcases h with h | h <;> omega
    refine ⟨hpos.1, hpos.2, ?_⟩
    have hnat := (Imo2019P4_assumed n k hpos.1 hpos.2).2 h
    have hc : (↑(Nat.factorial k) : ℤ) =
        ↑(∏ i ∈ Finset.range n, ((2 : ℕ) ^ n - (2 : ℕ) ^ i)) :=
      congrArg (fun x : ℕ => (x : ℤ)) hnat
    exact hc.trans hprod
  · rintro ⟨hn, hk, hint⟩
    apply (Imo2019P4_assumed n k hn hk).1
    have hc : (↑(Nat.factorial k) : ℤ) =
        ↑(∏ i ∈ Finset.range n, ((2 : ℕ) ^ n - (2 : ℕ) ^ i)) :=
      hint.trans hprod.symm
    exact_mod_cast hc
