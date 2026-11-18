import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b1_solution : ℕ × ℕ := (4, 1)

-- ===== assumed statement (antecedent) =====
theorem putnam_1976_b1_assumed
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
    (𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) - 2 * Int.floor ((n : ℝ) / (k : ℝ)))) Filter.atTop (nhds (Real.log 4 - 1)) := by
  have hIcc (n : ℕ) :
      (Finset.Icc 1 n).map (Nat.castEmbedding : ℕ ↪ ℤ) =
        Finset.Icc 1 (n : ℤ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy1, hyn⟩, rfl⟩
      change 1 ≤ (y : ℤ) ∧ (y : ℤ) ≤ (n : ℤ)
      omega
    · intro hx
      have hx0 : 0 ≤ x := by omega
      have hcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
      refine ⟨x.toNat, ?_, hcast⟩
      constructor <;> omega
  have heq :
      (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n,
        (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) =
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n,
        (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) -
          2 * Int.floor ((n : ℝ) / (k : ℝ)))) := by
    funext n
    rw [← hIcc n, Finset.sum_map]
    congr 1
    have hn2 : Int.floor (2 * (n : ℝ)) = (2 * n : ℕ) := by
      convert Int.floor_natCast (R := ℝ) (2 * n) using 1 <;> norm_num
    simp [Int.floor_div_natCast, hn2]
  have h := putnam_1976_b1_assumed
  rw [heq] at h
  simpa [putnam_1976_b1_solution] using h
