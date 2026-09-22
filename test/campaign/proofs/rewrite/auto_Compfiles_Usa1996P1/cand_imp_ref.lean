import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Usa1996P1_assumed :
    (∑ k ∈ Finset.Icc (1 : ℕ) 90,
        (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180)) / 90 =
      1 / Real.tan (Real.pi / 180) :=
  by
    sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Usa1996P1_refs :
    (1 / (90:ℝ)) * ∑ n ∈ Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by
  have hsum :
      (∑ n ∈ Finset.range 90,
          (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)) =
        ∑ k ∈ Finset.Icc (1 : ℕ) 90,
          (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180) := by
    refine Finset.sum_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢
      exact ⟨Nat.succ_le_succ (Nat.zero_le n), hn⟩
    · intro a ha b hb hab
      exact Nat.add_right_cancel hab
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      refine ⟨k - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        exact Nat.lt_of_lt_of_le
          (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk.1) Nat.zero_lt_one) hk.2
      · exact Nat.sub_add_cancel hk.1
    · intro n hn
      simp only [Nat.cast_add, Nat.cast_one]
  rw [hsum]
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using Usa1996P1_assumed
