import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))).re) / Real.log 2 = 13725 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution := by
  let P : ℂ :=
    ∏ a : Fin 2015, ∏ b : Fin 2015,
      (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))
  let Q : ℂ :=
    Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a ↦
      Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b ↦
        (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))
  have hPQ : P = Q := by
    dsimp [P, Q]
    have hc (n : ℕ) : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by norm_num
    simp_rw [hc]
    rw [Fin.prod_univ_eq_prod_range
      (fun a : ℕ ↦ ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * ((a + 1 : ℕ) : ℂ) *
          ((b.1 + 1 : ℕ) : ℂ) / 2015))) 2015]
    refine Finset.prod_bij' (fun a _ ↦ a + 1) (fun a _ ↦ a - 1) ?_ ?_ ?_ ?_ ?_
    · simp only [Finset.mem_range, Finset.mem_Icc]
      omega
    · simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    · simp only [Finset.mem_range]
      omega
    · simp only [Finset.mem_Icc]
      omega
    · intro a ha
      rw [Fin.prod_univ_eq_prod_range
        (fun b : ℕ ↦ (1 + Complex.exp (2 * Real.pi * Complex.I * ((a + 1 : ℕ) : ℂ) *
          ((b + 1 : ℕ) : ℂ) / 2015))) 2015]
      refine Finset.prod_bij' (fun b _ ↦ b + 1) (fun b _ ↦ b - 1) ?_ ?_ ?_ ?_ ?_
      · simp only [Finset.mem_range, Finset.mem_Icc]
        omega
      · simp only [Finset.mem_Icc, Finset.mem_range]
        omega
      · simp only [Finset.mem_range]
        omega
      · simp only [Finset.mem_Icc]
        omega
      · intro b hb
        congr 2
        push_cast
        ring
  have hQconj : starRingEnd ℂ Q = Q := by
    dsimp [Q]
    simp only [map_prod, map_add, map_one, ← Complex.exp_conj, map_mul,
      RCLike.conj_div, map_ofNat, Complex.conj_natCast, Complex.conj_I,
      Complex.conj_ofReal]
    let c : ℕ → ℕ := fun a ↦ if a = 2015 then 2015 else 2015 - a
    refine Finset.prod_bij' (fun a _ ↦ c a) (fun a _ ↦ c a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      dsimp [c]
      split_ifs <;> omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      dsimp [c]
      split_ifs <;> omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      by_cases h : a = 2015
      · simp [c, h]
      · have hne : 2015 - a ≠ 2015 := by omega
        simp only [c, if_neg h, if_neg hne]
        omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      by_cases h : a = 2015
      · simp [c, h]
      · have hne : 2015 - a ≠ 2015 := by omega
        simp only [c, if_neg h, if_neg hne]
        omega
    · intro a ha
      apply Finset.prod_congr rfl
      intro b hb
      simp only
      dsimp [c]
      split_ifs with h
      · subst a
        have hpos : Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (((2015 : ℕ) : ℂ) * b / 2015)) = 1 := by
          rw [show 2 * (Real.pi : ℂ) * Complex.I * (((2015 : ℕ) : ℂ) * b / 2015) =
              b * (2 * (Real.pi : ℂ) * Complex.I) by
            norm_num
            ring]
          simp
        have hneg : Complex.exp
            (2 * (Real.pi : ℂ) * -Complex.I * (((2015 : ℕ) : ℂ) * b / 2015)) = 1 := by
          rw [show 2 * (Real.pi : ℂ) * -Complex.I * (((2015 : ℕ) : ℂ) * b / 2015) =
              -(b * (2 * (Real.pi : ℂ) * Complex.I)) by
            norm_num
            ring]
          rw [Complex.exp_neg]
          simp
        rw [hpos, hneg]
      · have ha' : a < 2015 := by
          simp only [Finset.mem_Icc] at ha
          omega
        rw [show
          2 * (Real.pi : ℂ) * Complex.I * (((2015 - a : ℕ) : ℂ) * b / (2015 : ℂ)) =
            2 * (Real.pi : ℂ) * -Complex.I * ((a * b : ℂ) / (2015 : ℂ)) +
              b * (2 * (Real.pi : ℂ) * Complex.I) by
                push_cast [Nat.cast_sub ha'.le]
                field_simp
                ring]
        rw [Complex.exp_add]
        have hperiod : Complex.exp (b * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
          simpa using Complex.exp_nat_mul_two_pi_mul_I b
        rw [hperiod, mul_one]
  have hQreal : (Q.re : ℂ) = Q := Complex.conj_eq_iff_re.mp hQconj
  have h := problem_statement_assumed
  change Complex.log (Q.re : ℂ) / (Real.log 2 : ℂ) = (13725 : ℂ) at h
  rw [hQreal, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)] at h
  change Complex.log P / Complex.log 2 = putnam_2015_a3_solution
  simpa [putnam_2015_a3_solution, hPQ] using h

