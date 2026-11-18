import Mathlib

open Complex Real

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015))) / Real.log 2 : ℂ) = (13725 : ℂ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
  have prod_shift (f : ℕ → ℂ) :
      (∏ a : Fin 2015, f (a.1 + 1)) =
        ∏ a ∈ Finset.Icc (1 : ℕ) 2015, f a := by
    refine Finset.prod_bij (fun a _ => a.1 + 1) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_Icc]
      intro a ha
      omega
    · intro a₁ ha₁ a₂ ha₂ h
      change a₁.val + 1 = a₂.val + 1 at h
      apply Fin.ext
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      change (b - 1) + 1 = b
      omega
    · intro a ha
      rfl
  set_option maxRecDepth 10000 in
  have hprod :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      Finset.prod (Finset.Icc (1 : ℕ) 2015) (fun a =>
        Finset.prod (Finset.Icc (1 : ℕ) 2015) (fun b =>
          (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015)))) := by
    calc
      (∏ a : Fin 2015, ∏ b : Fin 2015,
          (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
          ∏ a : Fin 2015, ∏ b ∈ Finset.Icc (1 : ℕ) 2015,
            (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * b / 2015)) := by
              apply Finset.prod_congr rfl
              intro a ha
              simpa only [Nat.cast_add, Nat.cast_one] using
                (prod_shift (fun b =>
                  (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * b / 2015))))
      _ = ∏ a ∈ Finset.Icc (1 : ℕ) 2015, ∏ b ∈ Finset.Icc (1 : ℕ) 2015,
            (1 + Complex.exp (2 * Real.pi * Complex.I * a * b / 2015)) := by
              simpa only [Nat.cast_add, Nat.cast_one] using prod_shift (fun a =>
                Finset.prod (Finset.Icc (1 : ℕ) 2015) (fun b =>
                  (1 + Complex.exp (2 * Real.pi * Complex.I * a * b / 2015))))
      _ = Finset.prod (Finset.Icc (1 : ℕ) 2015) (fun a =>
            Finset.prod (Finset.Icc (1 : ℕ) 2015) (fun b =>
              (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015)))) := by
              simp only [mul_assoc]
  set_option maxHeartbeats 1000000 in
    have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [hprod, htwo, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2)]
  exact problem_statement_assumed
