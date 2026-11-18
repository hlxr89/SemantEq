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
  have hassumed :
      Tendsto (fun n : ℕ => ((1 : ℝ) / n) *
        ∑ k ∈ Finset.Icc (1 : ℤ) n,
          (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) atTop
        (𝓝 (Real.log 4 - 1)) := by
    simpa only [putnam_1976_b1_solution, Nat.cast_ofNat, Nat.cast_one] using
      putnam_1976_b1_assumed
  refine Filter.Tendsto.congr (fun n => ?_) hassumed
  have hsum :
      (∑ k ∈ Finset.Icc (1 : ℤ) n,
          (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) =
        ∑ k ∈ Finset.Icc 1 n,
          (Int.floor ((2 * (n : ℝ)) / (k : ℝ)) -
            2 * Int.floor ((n : ℝ) / (k : ℝ))) := by
    apply Finset.sum_bij' (fun (k : ℤ) _ => k.toNat)
      (fun (k : ℕ) _ => (k : ℤ))
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      have hk0 : 0 ≤ k := le_trans zero_le_one hk.1
      have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
      constructor
      · apply Int.ofNat_le.mp
        rw [hcast]
        exact hk.1
      · apply Int.ofNat_le.mp
        rw [hcast]
        exact hk.2
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨Int.ofNat_le.mpr hk.1, Int.ofNat_le.mpr hk.2⟩
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      exact Int.toNat_of_nonneg (le_trans zero_le_one hk.1)
    · intro k _
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg (Int.natCast_nonneg k)]
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hcast : (k.toNat : ℤ) = k :=
        Int.toNat_of_nonneg (le_trans zero_le_one hk.1)
      have hreal : (k.toNat : ℝ) = (k : ℝ) := by
        rw [← Int.cast_natCast]
        exact congrArg (fun z : ℤ => (z : ℝ)) hcast
      have hnum2 : 2 * (n : ℝ) = ((2 * (n : ℤ) : ℤ) : ℝ) := by
        rw [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      have hnum1 : (n : ℝ) = ((n : ℤ) : ℝ) := by
        rw [Int.cast_natCast]
      rw [hreal, hnum2, hnum1]
      simp only [Int.floor_div_cast_of_nonneg (le_trans zero_le_one hk.1),
        Int.floor_intCast]
      have hfloor (z : ℤ) : Int.floor z = z := by
        change z = z
        rfl
      rw [hfloor, hfloor]
  rw [hsum]
