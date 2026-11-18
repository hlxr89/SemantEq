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
  have shift_prod (f : ℕ → ℂ) :
      (∏ k : Fin 2015, f (k.1 + 1)) = ∏ k ∈ Finset.Icc 1 2015, f k := by
    rw [Fin.prod_univ_eq_prod_range (fun k => f (k + 1)) 2015]
    refine Finset.prod_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_range, Finset.mem_Icc]
      omega
    · intro a ha b hb hab
      dsimp at hab
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨b - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · dsimp
        omega
    · intro a ha
      rfl
  let f : ℕ → ℕ → ℂ := fun a b =>
    1 + Complex.exp (2 * Real.pi * Complex.I * (↑(a * b) / 2015))
  have hproducts :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      ∏ a ∈ Finset.Icc (1 : ℕ) 2015, ∏ b ∈ Finset.Icc (1 : ℕ) 2015, f a b := by
    calc
      _ = ∏ a : Fin 2015, ∏ b : Fin 2015, f (a.1 + 1) (b.1 + 1) := by
        apply Finset.prod_congr rfl
        intro a ha
        apply Finset.prod_congr rfl
        intro b hb
        dsimp [f]
        congr 2
        push_cast
        ring
      _ = ∏ a : Fin 2015, ∏ b ∈ Finset.Icc (1 : ℕ) 2015, f (a.1 + 1) b := by
        apply Finset.prod_congr rfl
        intro a ha
        exact shift_prod (f (a.1 + 1))
      _ = ∏ a ∈ Finset.Icc (1 : ℕ) 2015, ∏ b ∈ Finset.Icc (1 : ℕ) 2015, f a b := by
        exact shift_prod (fun a => ∏ b ∈ Finset.Icc (1 : ℕ) 2015, f a b)
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hproducts]
  simpa [putnam_2015_a3_solution] using putnam_2015_a3_assumed
