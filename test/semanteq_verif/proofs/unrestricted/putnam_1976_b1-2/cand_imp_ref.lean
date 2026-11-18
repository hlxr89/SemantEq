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
    (𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) :=
by
  have hsum (n : ℕ) :
      (∑ k ∈ Finset.Icc 1 n,
        (Int.floor ((2 * n : ℝ) / (k : ℝ)) - 2 * Int.floor ((n : ℝ) / (k : ℝ)))) =
      ∑ k ∈ Finset.Icc (1 : ℤ) n,
        (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k)) := by
    apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ))
    · simp
    · simp
    · intro k hk
      refine ⟨k.toNat, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hk ⊢
        constructor <;> omega
      · exact Int.toNat_of_nonneg (by
          have := (Finset.mem_Icc.mp hk).1
          omega)
    · intro k hk
      rw [Int.floor_div_natCast, Int.floor_div_natCast]
      have htwo : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [htwo, ← Nat.cast_mul, Int.floor_natCast, Int.floor_natCast]
      norm_num
  convert problem_statement_assumed using 1
  · funext n
    have hcast :
        (∑ k ∈ Finset.Icc 1 n,
          ((Int.floor ((2 * n : ℝ) / (k : ℝ)) : ℝ) -
            2 * (Int.floor ((n : ℝ) / (k : ℝ)) : ℝ))) =
        ((∑ k ∈ Finset.Icc 1 n,
          (Int.floor ((2 * n : ℝ) / (k : ℝ)) -
            2 * Int.floor ((n : ℝ) / (k : ℝ)))) : ℤ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      norm_num
    rw [hcast, hsum n]
  · norm_num
