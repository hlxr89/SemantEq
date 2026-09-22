import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Usa1996P1_assumed :
    (∑ k ∈ Finset.Icc (1 : ℕ) 90,
        (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180)) / 90 =
      1 / Real.tan (Real.pi / 180) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Usa1996P1_refs :
    (1 / (90:ℝ)) * ∑ n ∈ Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by
  have hsum :
      (∑ n ∈ Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)) =
        ∑ k ∈ Finset.Icc (1 : ℕ) 90,
          (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180) := by
    refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_range, Finset.mem_Icc]
      omega
    · intro a ha b hb hab
      dsimp at hab
      omega
    · simp only [Finset.mem_Icc, Finset.mem_range]
      intro k hk
      refine ⟨k - 1, ?_, ?_⟩
      · omega
      · omega
    · norm_num
  calc
    _ = (∑ k ∈ Finset.Icc (1 : ℕ) 90,
        (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180)) / 90 := by
          rw [← hsum]
          ring
    _ = _ := Usa1996P1_assumed
