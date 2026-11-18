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
  classical
  have prod_fin_eq_Icc (f : ℕ → ℕ → ℂ) :
      (∏ a : Fin 2015, ∏ b : Fin 2015, f (a.1 + 1) (b.1 + 1)) =
        ∏ a ∈ Finset.Icc 1 2015, ∏ b ∈ Finset.Icc 1 2015, f a b := by
    apply Finset.prod_bij (fun a _ => a.1 + 1)
    · simp
    · intro a _ a' _ h
      apply Fin.ext
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      refine ⟨⟨a - 1, by omega⟩, by simp, ?_⟩
      exact Nat.sub_add_cancel ha.1
    · intro a _
      apply Finset.prod_bij (fun b _ => b.1 + 1)
      · simp
      · intro b _ b' _ h
        apply Fin.ext
        omega
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        refine ⟨⟨b - 1, by omega⟩, by simp, ?_⟩
        exact Nat.sub_add_cancel hb.1
      · simp
  have hprod :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
          (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015)) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
      prod_fin_eq_Icc
        (fun a b => 1 + Complex.exp
          (2 * Real.pi * Complex.I * (a : ℂ) * (b : ℂ) / 2015))
  rw [hprod]
  have h := problem_statement_assumed
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)] at h
  simpa only [putnam_2015_a3_solution] using h
