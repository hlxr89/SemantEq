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
  have hsum (n : ℕ) :
      (∑ x ∈ Finset.Icc 1 n,
        ((⌊(2 * n : ℝ) / (x : ℝ)⌋ : ℝ) - 2 * (⌊(n : ℝ) / (x : ℝ)⌋ : ℝ))) =
      ∑ x ∈ Finset.Icc (1 : ℤ) n,
        ((Int.floor ((2 * n) / x) : ℝ) - 2 * (Int.floor (n / x) : ℝ)) := by
    refine Finset.sum_bij (M := ℝ) (s := Finset.Icc 1 n) (t := Finset.Icc (1 : ℤ) n)
      (f := fun x : ℕ ↦
        ((⌊(2 * n : ℝ) / (x : ℝ)⌋ : ℝ) - 2 * (⌊(n : ℝ) / (x : ℝ)⌋ : ℝ)))
      (g := fun x : ℤ ↦
        (Int.floor ((2 * n) / x) : ℝ) - 2 * (Int.floor (n / x) : ℝ))
      (fun (x : ℕ) _ ↦ (x : ℤ)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_Icc] at hx ⊢
      change (1 : ℤ) ≤ (x : ℤ) ∧ (x : ℤ) ≤ (n : ℤ)
      exact_mod_cast hx
    · intro a₁ ha₁ a₂ ha₂ h
      exact Int.ofNat_inj.mp h
    · intro b hb
      rw [Finset.mem_Icc] at hb
      have hb0 : 0 ≤ b := le_trans (by omega) hb.1
      refine ⟨b.toNat, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · exact Int.toNat_of_nonneg hb0
    · intro a ha
      dsimp
      norm_cast
      rw [Int.floor_div_natCast, Int.floor_div_natCast]
      rw [Int.floor_natCast, Int.floor_natCast]
      rw [Int.ofNat_ediv_ofNat, Int.ofNat_ediv_ofNat]
      change Int.ofNat (2 * n / a) - Int.ofNat (2 * (n / a)) = _
      exact Int.subNatNat_eq_coe.symm
  have hfun :
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) * ∑ k ∈ Finset.Icc 1 n,
        ((⌊(2 * n : ℝ) / (k : ℝ)⌋ : ℝ) - 2 * (⌊(n : ℝ) / (k : ℝ)⌋ : ℝ))) =
      (fun n : ℕ => ((1 : ℝ) / n) * ∑ k ∈ Finset.Icc (1 : ℤ) n,
        (Int.floor ((2 * n) / k) - 2 * Int.floor (n / k))) := by
    funext n
    simp only [Int.cast_sum, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    rw [hsum]
  rw [← hfun]
  simpa [putnam_1976_b1_solution] using problem_statement_assumed
