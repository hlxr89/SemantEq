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
    have hle : (2 : ℕ) ^ i ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by decide) (Finset.mem_range.mp hi).le
    simpa using (Nat.cast_sub (R := ℤ) hle)
  constructor
  · intro hmem
    have hpos : 0 < n ∧ 0 < k := by
      simp [solution_set] at hmem
      rcases hmem with h | h <;> omega
    have hmem' : (n, k) ∈ Imo2019P4_solution := by
      change (n, k) ∈ solution_set
      exact hmem
    have hnat := (Imo2019P4_assumed n k hpos.1 hpos.2).2 hmem'
    have hint :
        (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) := by
      exact (congrArg (fun x : ℕ => (x : ℤ)) hnat).trans hprod
    exact ⟨hpos.1, hpos.2, hint⟩
  · rintro ⟨hn, hk, hint⟩
    have hcast :
        (↑(Nat.factorial k) : ℤ) =
          ↑(∏ i ∈ Finset.range n, ((2 : ℕ) ^ n - (2 : ℕ) ^ i)) :=
      hint.trans hprod.symm
    have hnat : Nat.factorial k = ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) := by
      exact_mod_cast hcast
    have hmem := (Imo2019P4_assumed n k hn hk).1 hnat
    change (n, k) ∈ Imo2019P4_solution
    exact hmem
