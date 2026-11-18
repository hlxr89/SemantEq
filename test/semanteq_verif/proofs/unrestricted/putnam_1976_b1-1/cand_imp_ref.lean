import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b1_solution : ℕ × ℕ := (4, 1)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) - 2 * Int.floor ((n : ℝ) / (k : ℝ)))) Filter.atTop (nhds (Real.log 4 - 1)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1976_b1
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
    (𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) :=
by
  have floor_real_nat_div (a b : ℕ) :
      Int.floor ((a : ℝ) / (b : ℝ)) = (a / b : ℕ) := by
    calc
      Int.floor ((a : ℝ) / (b : ℝ)) =
          Int.floor (((a : ℚ) / (b : ℚ) : ℚ) : ℝ) := by norm_num
      _ = Int.floor ((a : ℚ) / (b : ℚ)) := Rat.floor_cast _
      _ = (a / b : ℕ) := Rat.floor_natCast_div_natCast a b
  have floor_int_nat_div (a b : ℕ) :
      Int.floor (((a : ℤ) / (b : ℤ) : ℤ)) =
        Int.floor ((a : ℝ) / (b : ℝ)) := by
    calc
      Int.floor (((a : ℤ) / (b : ℤ) : ℤ)) = (a / b : ℕ) := by norm_cast
      _ = Int.floor ((a : ℝ) / (b : ℝ)) := (floor_real_nat_div a b).symm
  have sum_eq (n : ℕ) :
      (∑ k ∈ Finset.Icc 1 n,
          (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) -
            2 * Int.floor ((n : ℝ) / (k : ℝ)))) =
        ∑ k ∈ Finset.Icc (1 : ℤ) n,
          (Int.floor ((2*n)/k) - 2*Int.floor (n/k)) := by
    refine Finset.sum_bij (fun k _ => (k : ℤ)) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_Icc]
      intro k hk
      exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
    · intro a₁ ha₁ a₂ ha₂ h
      exact Int.ofNat_inj.mp h
    · simp only [Finset.mem_Icc]
      intro k hk
      have hk0 : 0 ≤ k := le_trans (by omega) hk.1
      refine ⟨k.toNat, ⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · exact Int.toNat_of_nonneg hk0
    · intro k hk
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        congrArg₂ (fun x y : ℤ => x - 2 * y)
          (floor_int_nat_div (2 * n) k).symm
          (floor_int_nat_div n k).symm
  have fun_eq :
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n,
        (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) -
          2 * Int.floor ((n : ℝ) / (k : ℝ)))) =
      (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n,
        (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) := by
    funext n
    rw [sum_eq n]
  rw [← fun_eq]
  simpa [putnam_1976_b1_solution] using problem_statement_assumed
