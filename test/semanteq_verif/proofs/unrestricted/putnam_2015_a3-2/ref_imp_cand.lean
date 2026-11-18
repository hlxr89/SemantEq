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
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))).re) / Real.log 2 = 13725 := by
  let P : ℂ := ∏ a : Fin 2015, ∏ b : Fin 2015,
    (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))
  let Q : ℂ := Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
    Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
      (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))
  have hPQ : P = Q := by
    let e : Fin 2015 ≃ {n : ℕ // n ∈ Finset.Icc 1 2015} :=
      { toFun := fun a => ⟨a.1 + 1, by simp⟩
        invFun := fun n => ⟨n.1 - 1, by
          have hn := n.property
          simp only [Finset.mem_Icc] at hn
          omega⟩
        left_inv := by intro a; ext; simp
        right_inv := by
          intro n
          have hn := n.property
          ext
          simp only [Finset.mem_Icc] at hn
          simp [hn.1] }
    dsimp [P, Q]
    rw [show (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
          (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))) =
        ∏ a : {n : ℕ // n ∈ Finset.Icc 1 2015},
          ∏ b : {n : ℕ // n ∈ Finset.Icc 1 2015},
            (1 + Complex.exp (2 * Real.pi * Complex.I * (((a.1 * b.1 : ℕ) : ℂ) / (2015 : ℂ)))) by
      rw [Finset.prod_subtype (p := fun x => x ∈ Finset.Icc 1 2015) _ (by simp)]
      apply Fintype.prod_congr
      intro a
      rw [Finset.prod_subtype (p := fun x => x ∈ Finset.Icc 1 2015) _ (by simp)]
      apply Fintype.prod_congr
      intro b
      congr 2
      norm_cast]
    apply Fintype.prod_equiv e _ _
    intro a
    apply Fintype.prod_equiv e _ _
    intro b
    congr 2
    simp [e]
    ring
  have h := putnam_2015_a3_assumed
  change Complex.log P / Complex.log 2 = (13725 : ℂ) at h
  have hlog2R : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlog2eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2)).symm
  have hlog2 : Complex.log (2 : ℂ) ≠ 0 := by
    rw [hlog2eq]
    exact_mod_cast hlog2R
  have hP0 : P ≠ 0 := by
    intro hP
    rw [hP] at h
    norm_num at h
  have hlogP : Complex.log P = (13725 : ℂ) * Complex.log 2 :=
    (div_eq_iff hlog2).mp h
  have hPval : P = (Real.exp (13725 * Real.log 2) : ℝ) := by
    rw [← Complex.exp_log hP0, hlogP, hlog2eq]
    norm_num
  change Complex.log (Q.re : ℂ) / (Real.log 2 : ℂ) = 13725
  rw [← hPQ, hPval]
  simp only [Complex.ofReal_re]
  rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos _)), Real.log_exp]
  apply (div_eq_iff _).2
  · rw [Complex.ofReal_mul]
    norm_num
  · exact_mod_cast hlog2R
