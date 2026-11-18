import Mathlib

open Complex Real

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

private lemma fin_prod_eq_Icc_prod (f : ℂ → ℂ) :
    (∏ a : Fin 2015, f ((a.1 : ℂ) + 1)) =
      ∏ a ∈ Finset.Icc (1 : ℕ) 2015, f (a : ℂ) := by
  simpa using (Finset.prod_bij (fun (a : Fin 2015) _ => a.1 + 1)
    (fun a _ => by simp)
    (fun a _ b _ h => by
      dsimp at h
      exact Fin.ext (by omega))
    (fun b hb => by
      simp only [Finset.mem_Icc] at hb
      refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega)
    (fun a _ => by norm_num) :
    (∏ a ∈ Finset.univ, f ((a.1 : ℂ) + 1)) =
      ∏ a ∈ Finset.Icc (1 : ℕ) 2015, f (a : ℂ))

-- ===== assumed statement (antecedent) =====
theorem putnam_2015_a3_assumed :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015))) / Real.log 2 : ℂ) = (13725 : ℂ) := by
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  change _ = putnam_2015_a3_solution
  have hp :
      (∏ a ∈ Finset.Icc (1 : ℕ) 2015, ∏ b ∈ Finset.Icc (1 : ℕ) 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015))) =
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) := by
    rw [fin_prod_eq_Icc_prod (fun x => ∏ b : Fin 2015,
      (1 + Complex.exp (2 * Real.pi * Complex.I * x * (b.1 + 1) / 2015)))]
    apply Finset.prod_congr rfl
    intro a ha
    rw [fin_prod_eq_Icc_prod (fun x =>
      (1 + Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * x / 2015)))]
    simp [mul_assoc]
  rw [hp]
  exact putnam_2015_a3_assumed
