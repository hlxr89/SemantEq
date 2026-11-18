import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b1_solution : ℕ × ℕ := (4, 1)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) * ∑ k ∈ Finset.Icc 1 n, ((⌊(2 * n : ℝ) / (k : ℝ)⌋ : ℝ) - 2 * (⌊(n : ℝ) / (k : ℝ)⌋ : ℝ))) Filter.atTop (nhds (Real.log 4 - 1)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1976_b1
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
    (𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) := by
  have hfun :
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) * ∑ k ∈ Finset.Icc 1 n,
        ((⌊(2 * n : ℝ) / (k : ℝ)⌋ : ℝ) - 2 * (⌊(n : ℝ) / (k : ℝ)⌋ : ℝ))) =
      (fun n : ℕ => ((1 : ℝ) / n) * ∑ k ∈ Finset.Icc (1 : ℤ) n,
        (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) := by
    funext n
    congr 1
    symm
    push_cast
    apply Finset.sum_bij (fun (k : ℤ) _ => k.toNat)
    · simp only [Finset.mem_Icc]
      omega
    · simp only [Finset.mem_Icc]
      omega
    · simp only [Finset.mem_Icc]
      intro b hb
      refine ⟨(b : ℤ), ?_, ?_⟩
      · omega
      · simp
    · simp only [Finset.mem_Icc]
      intro k hk
      have hk0 : 0 ≤ k := by omega
      have hcast : (k.toNat : ℝ) = (k : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hk0
      rw [hcast]
      have hfloor : ⌊(2 : ℝ) * (n : ℝ)⌋ = 2 * (n : ℤ) := by
        convert Int.floor_intCast (R := ℝ) (2 * (n : ℤ)) using 1 <;> norm_num
      simp [Int.floor_div_cast_of_nonneg hk0, hfloor]
  rw [← hfun]
  simpa [putnam_1976_b1_solution] using problem_statement_assumed
