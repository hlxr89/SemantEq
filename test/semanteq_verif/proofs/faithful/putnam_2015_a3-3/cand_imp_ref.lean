import Mathlib

open Complex Real

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (b : ℂ) / 2015)) / Real.log 2 = 13725 := by sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
  have hreindex (f : ℂ → ℂ) :
      (∏ i : Fin 2015, f ((i.1 : ℂ) + 1)) =
        ∏ i ∈ Finset.Icc (1 : ℕ) 2015, f (i : ℂ) := by
    calc
      _ = ∏ i ∈ Finset.range 2015, f ((i + 1 : ℕ) : ℂ) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (Fin.prod_univ_eq_prod_range (fun i : ℕ => f ((i + 1 : ℕ) : ℂ)) 2015)
      _ = _ := by
        apply Finset.prod_bij (fun (i : ℕ) _ => i + 1)
        · simp only [Finset.mem_Icc, Finset.mem_range]
          omega
        · intro a₁ ha₁ a₂ ha₂ h
          omega
        · intro b hb
          simp only [Finset.mem_Icc] at hb
          refine ⟨b - 1, ?_, ?_⟩
          · simpa only [Finset.mem_range] using
              (lt_of_lt_of_le
                (Nat.sub_lt (n := b) (m := 1) hb.1 (by norm_num)) hb.2)
          · omega
        · intros
          simp [Nat.cast_add, Nat.cast_one]
  have hp :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
          (1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (b : ℂ) / 2015) := by
    calc
      _ = ∏ a ∈ Finset.Icc (1 : ℕ) 2015,
          ∏ b : Fin 2015,
            (1 + Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * ((b.1 : ℂ) + 1) / 2015)) :=
        hreindex (fun a : ℂ => ∏ b : Fin 2015,
          (1 + Complex.exp (2 * Real.pi * Complex.I * a * ((b.1 : ℂ) + 1) / 2015)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro a ha
        exact hreindex (fun b =>
          (1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * b / 2015))
  rw [hp]
  simpa only [putnam_2015_a3_solution,
    Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)] using
    problem_statement_assumed
