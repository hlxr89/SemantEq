import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b1_solution : ℕ × ℕ := (4, 1)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) * ∑ k ∈ Finset.Icc 1 n, ((⌊(2 * n : ℝ) / (k : ℝ)⌋ : ℝ) - 2 * (⌊(n : ℝ) / (k : ℝ)⌋ : ℝ))) Filter.atTop (nhds (Real.log 4 - 1)) :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1976_b1
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
    (𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) := by
  have hindex (n : ℕ) :
      (Finset.Icc 1 n).map Nat.castEmbedding = Finset.Icc (1 : ℤ) n := by
    ext z
    simp only [Finset.mem_map, Finset.mem_Icc, Nat.castEmbedding_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact_mod_cast ha
    · intro hz
      have hz0 : 0 ≤ z := le_trans (show (0 : ℤ) ≤ 1 from zero_le_one) hz.1
      refine ⟨z.toNat, ?_, Int.toNat_of_nonneg hz0⟩
      rw [← Int.toNat_of_nonneg hz0] at hz
      exact_mod_cast hz
  have hfloor (a k : ℕ) :
      ⌊(a : ℝ) / (k : ℝ)⌋ = ((a / k : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_natCast]
    exact (Int.natCast_div a k).symm
  have hfloor_two (n k : ℕ) :
      ⌊(2 * n : ℝ) / (k : ℝ)⌋ = (((2 * n) / k : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfloor (2 * n) k
  have hsum (n : ℕ) :
      ((↑(∑ k ∈ Finset.Icc (1 : ℤ) n,
          (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n,
          ((⌊(2 * n : ℝ) / (k : ℝ)⌋ : ℝ) -
            2 * (⌊(n : ℝ) / (k : ℝ)⌋ : ℝ)) := by
    rw [← hindex n]
    simp only [Int.floor_int, id_eq, Finset.sum_sub_distrib, Finset.sum_map,
      Nat.castEmbedding_apply, Int.cast_sub, Int.cast_sum, Int.cast_mul,
      Int.cast_ofNat, hfloor_two, Int.natCast_ediv, Nat.cast_mul,
      Nat.cast_ofNat, hfloor]
  simpa only [putnam_1976_b1_solution, hsum, Nat.cast_ofNat, Nat.cast_one] using
    problem_statement_assumed
