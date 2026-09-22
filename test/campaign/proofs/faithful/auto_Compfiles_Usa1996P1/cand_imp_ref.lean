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
  have h := Usa1996P1_assumed
  have hfin : Finset.Icc (1 : ℕ) 90 =
      (Finset.range 90).image (fun n => n + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega
  rw [hfin, Finset.sum_image] at h
  · simpa [div_eq_mul_inv, mul_comm] using h
  · intro a _ b _ hab
    exact Nat.add_right_cancel hab
