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
/-- Determine all positive integers n,k that satisfy the equation

  k! = (2ⁿ - 2⁰)(2ⁿ - 2¹) ... (2ⁿ - 2ⁿ⁻¹). -/
theorem Imo2019P4 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.factorial k = ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) ↔
      (n, k) ∈ Imo2019P4_solution := by
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
  · intro h
    have hint :
        (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) := by
      exact (congrArg (fun x : ℕ => (x : ℤ)) h).trans hprod
    have hmem : (n, k) ∈ solution_set :=
      (Imo2019P4_refs_assumed n k).2 ⟨hn, hk, hint⟩
    change (n, k) ∈ solution_set
    exact hmem
  · intro hmem
    change (n, k) ∈ solution_set at hmem
    have hint := ((Imo2019P4_refs_assumed n k).1 hmem).2.2
    have hcast :
        (↑(Nat.factorial k) : ℤ) =
          ↑(∏ i ∈ Finset.range n, ((2 : ℕ) ^ n - (2 : ℕ) ^ i)) :=
      hint.trans hprod.symm
    exact_mod_cast hcast
