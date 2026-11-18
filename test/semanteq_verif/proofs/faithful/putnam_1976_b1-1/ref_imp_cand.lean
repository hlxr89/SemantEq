import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b1_solution : ℕ × ℕ := (4, 1)

-- ===== assumed statement (antecedent) =====
theorem putnam_1976_b1_assumed
: Tendsto (fun n : ℕ => ((1 : ℝ)/n)*∑ k ∈ Finset.Icc (1 : ℤ) n, (Int.floor ((2*n)/k) - 2*Int.floor (n/k))) atTop
    (𝓝 (Real.log putnam_1976_b1_solution.1 - putnam_1976_b1_solution.2)) :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) - 2 * Int.floor ((n : ℝ) / (k : ℝ)))) Filter.atTop (nhds (Real.log 4 - 1)) := by
  have hsum (n : ℕ) :
      (∑ k ∈ Finset.Icc (1 : ℤ) n,
          (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) =
        ∑ k ∈ Finset.Icc 1 n,
          (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) -
            2 * Int.floor ((n : ℝ) / (k : ℝ))) := by
    symm
    apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ))
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb hab
      exact_mod_cast hab
    · intro b hb
      have hb0 : 0 ≤ b := by
        simp only [Finset.mem_Icc] at hb
        omega
      have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      refine ⟨b.toNat, ?_, hbcast⟩
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro k hk
      have h2n : ⌊(2 : ℝ) * (n : ℝ)⌋ = (2 : ℤ) * (n : ℤ) := by
        calc
          ⌊(2 : ℝ) * (n : ℝ)⌋ = ⌊((2 * n : ℕ) : ℝ)⌋ := by norm_num
          _ = ((2 * n : ℕ) : ℤ) := Int.floor_natCast _
          _ = (2 : ℤ) * (n : ℤ) := by norm_num
      simp [Int.floor_div_natCast, h2n]
  have hfun :
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n,
        (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) -
          2 * Int.floor ((n : ℝ) / (k : ℝ)))) =
      (fun n : ℕ => ((1 : ℝ) / n) * ∑ k ∈ Finset.Icc (1 : ℤ) n,
        (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) := by
    funext n
    rw [hsum]
  rw [hfun]
  simpa [putnam_1976_b1_solution] using putnam_1976_b1_assumed
