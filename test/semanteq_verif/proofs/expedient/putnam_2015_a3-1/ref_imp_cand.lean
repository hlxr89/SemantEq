import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem putnam_2015_a3_assumed :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * (↑(a * b) / 2015)))) / Real.log 2 = 13725 := by
  classical
  have hprod :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
          (1 + Complex.exp (2 * Real.pi * Complex.I * (↑(a * b) / 2015))) := by
    apply Finset.prod_bij (fun a _ => a.1 + 1)
    · intro a ha
      simp only [Finset.mem_Icc]
      omega
    · intro a₁ ha₁ a₂ ha₂ h
      apply Fin.ext
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      refine ⟨⟨a - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      exact Nat.sub_add_cancel ha.1
    · intro a ha
      apply Finset.prod_bij (fun b _ => b.1 + 1)
      · intro b hb
        simp only [Finset.mem_Icc]
        omega
      · intro b₁ hb₁ b₂ hb₂ h
        apply Fin.ext
        omega
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Nat.sub_add_cancel hb.1
      · intro b hb
        congr 2
        push_cast
        ring
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2), ← hprod]
  simpa [putnam_2015_a3_solution] using putnam_2015_a3_assumed
