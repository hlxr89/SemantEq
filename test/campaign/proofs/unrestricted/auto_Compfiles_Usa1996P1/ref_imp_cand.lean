import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Usa1996P1_refs_assumed :
    (1 / (90:ℝ)) * ∑ n ∈ Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Usa1996P1 :
    (∑ k ∈ Finset.Icc (1 : ℕ) 90,
        (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180)) / 90 =
      1 / Real.tan (Real.pi / 180) :=
  by
    have hsum :
        (∑ n ∈ Finset.range 90,
            (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)) =
          ∑ k ∈ Finset.Icc (1 : ℕ) 90,
            (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180) := by
      apply Finset.sum_bij (fun n _ => n + 1)
      · intro n hn
        simp only [Finset.mem_Icc]
        constructor
        · omega
        · exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
      · intro a₁ ha₁ a₂ ha₂ h
        omega
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨k - 1, ?_, ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · omega
      · intro n hn
        push_cast
        ring
    rw [← hsum]
    rw [← Usa1996P1_refs_assumed]
    ring
