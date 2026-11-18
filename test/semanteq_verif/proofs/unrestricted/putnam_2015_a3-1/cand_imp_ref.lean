import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * (↑(a * b) / 2015)))) / Real.log 2 = 13725 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
  let e : Fin 2015 ≃ {n : ℕ // n ∈ Finset.Icc 1 2015} :=
    Equiv.ofBijective
      (fun a => ⟨a.1 + 1, by simp only [Finset.mem_Icc]; omega⟩)
      (by
        constructor
        · intro a b hab
          apply Fin.ext
          have := congrArg Subtype.val hab
          change a.1 + 1 = b.1 + 1 at this
          omega
        · intro b
          refine ⟨⟨b.1 - 1, ?_⟩, ?_⟩
          · have hb := b.2
            simp only [Finset.mem_Icc] at hb
            omega
          · apply Subtype.ext
            change b.1 - 1 + 1 = b.1
            have hb := b.2
            simp only [Finset.mem_Icc] at hb
            omega)
  have hindex (f : ℕ → ℂ) :
      (∏ a : Fin 2015, f (a.1 + 1)) = ∏ a ∈ Finset.Icc 1 2015, f a := by
    calc
      (∏ a : Fin 2015, f (a.1 + 1)) =
          ∏ a : {n : ℕ // n ∈ Finset.Icc 1 2015}, f a.1 := by
            apply Fintype.prod_equiv e
            intro a
            rfl
      _ = ∏ a ∈ Finset.Icc 1 2015, f a := by
            symm
            apply Finset.prod_subtype
            intro a
            rfl
  let F : ℕ → ℕ → ℂ := fun a b =>
    1 + Complex.exp (2 * Real.pi * Complex.I * (↑(a * b) / 2015))
  have hprod :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      ∏ a ∈ Finset.Icc 1 2015, ∏ b ∈ Finset.Icc 1 2015, F a b := by
    calc
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
          ∏ a : Fin 2015, ∏ b : Fin 2015, F (a.1 + 1) (b.1 + 1) := by
            apply Finset.prod_congr rfl
            intro a ha
            apply Finset.prod_congr rfl
            intro b hb
            simp only [F]
            congr 2
            push_cast
            ring
      _ = ∏ a ∈ Finset.Icc 1 2015, ∏ b : Fin 2015, F a (b.1 + 1) :=
        hindex (fun a => ∏ b : Fin 2015, F a (b.1 + 1))
      _ = ∏ a ∈ Finset.Icc 1 2015, ∏ b ∈ Finset.Icc 1 2015, F a b := by
        apply Finset.prod_congr rfl
        intro a ha
        exact hindex (F a)
  rw [hprod]
  simpa only [F, putnam_2015_a3_solution, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)] using
    problem_statement_assumed
