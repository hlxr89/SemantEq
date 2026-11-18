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
  have hIcc : ∀ f : ℕ → ℂ,
      (∏ k ∈ Finset.Icc (1 : ℕ) 2015, f k) = ∏ k : Fin 2015, f (k.1 + 1) := by
    intro f
    refine Finset.prod_bij (fun k hk => ⟨k - 1, by simp only [Finset.mem_Icc] at hk; omega⟩) ?_ ?_ ?_ ?_
    · simp
    · intro a ha b hb hab
      have hab' := congrArg Fin.val hab
      simp only at hab'
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      refine ⟨b.1 + 1, ?_, ?_⟩
      · simp
      · apply Fin.ext
        simp
    · intro a ha
      change f a = f ((a - 1) + 1)
      simp only [Finset.mem_Icc] at ha
      congr 1
      omega
  have hprod :
      (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))) =
      (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) := by
    rw [hIcc]
    apply Finset.prod_congr rfl
    intro a ha
    rw [hIcc]
    apply Finset.prod_congr rfl
    intro b hb
    congr 2
    push_cast
    ring
  let P : ℂ := ∏ a : Fin 2015, ∏ b : Fin 2015,
    (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))
  have hlog2 : Complex.log (2 : ℂ) ≠ 0 := by
    change Complex.log ((2 : ℝ) : ℂ) ≠ 0
    intro h
    have h' := congrArg Complex.re h
    rw [Complex.log_ofReal_re] at h'
    norm_num at h'
  have hpne : P ≠ 0 := by
    intro hp
    have h := putnam_2015_a3_assumed
    change Complex.log P / Complex.log 2 = (13725 : ℂ) at h
    rw [hp, Complex.log_zero, zero_div] at h
    norm_num at h
  have hlog : Complex.log P = (13725 : ℂ) * Complex.log 2 := by
    apply (div_eq_iff hlog2).mp
    exact putnam_2015_a3_assumed
  have hpval : P = (2 : ℂ) ^ 13725 := by
    have h := congrArg Complex.exp hlog
    rw [Complex.exp_log hpne] at h
    rw [← Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0), ← Complex.exp_nat_mul]
    exact h
  have hreal : (P.re : ℂ) = P := by
    have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    have hpval' : P = (((2 : ℝ) : ℂ) ^ 13725) :=
      hpval.trans (congrArg (fun z : ℂ => z ^ 13725) htwo)
    apply Complex.conj_eq_iff_re.mp
    rw [hpval']
    rw [map_pow]
    exact congrArg (fun z : ℂ => z ^ 13725) (Complex.conj_ofReal 2)
  rw [hprod]
  change Complex.log (P.re : ℂ) / (Real.log 2 : ℂ) = (13725 : ℂ)
  rw [hreal, Complex.ofReal_log (show (0 : ℝ) ≤ 2 by norm_num)]
  exact putnam_2015_a3_assumed
