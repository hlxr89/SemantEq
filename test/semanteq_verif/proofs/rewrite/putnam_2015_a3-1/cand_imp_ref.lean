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
  have fin_prod_eq_Icc (f : ℂ → ℂ) :
      (∏ i : Fin 2015, f (i.1 + 1)) =
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun i => f i := by
    rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) 2015]
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_add, Nat.cast_one, Nat.add_comm]
  have fin_prod₂_eq_Icc (f : ℂ → ℂ → ℂ) :
      (∏ a : Fin 2015, ∏ b : Fin 2015, f (a.1 + 1) (b.1 + 1)) =
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
          Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => f a b := by
    rw [fin_prod_eq_Icc (fun a => ∏ b : Fin 2015, f a (b.1 + 1))]
    apply Finset.prod_congr rfl
    intro a ha
    exact fin_prod_eq_Icc (f a)
  rw [fin_prod₂_eq_Icc (fun a b =>
    1 + Complex.exp (2 * Real.pi * Complex.I * a * b / 2015))]
  simpa only [Nat.cast_mul, div_eq_mul_inv, mul_assoc, Complex.ofNat_log] using
    problem_statement_assumed
