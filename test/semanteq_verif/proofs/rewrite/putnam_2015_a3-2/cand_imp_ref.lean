import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))).re) / Real.log 2 = 13725 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
set_option maxRecDepth 10000
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
  classical
  let P : ℂ := ∏ a : Fin 2015, ∏ b : Fin 2015,
    (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))
  let Q : ℂ := Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
    Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
      (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))
  have hindex_one (F : ℂ → ℂ) :
      (∏ a : Fin 2015, F (a.1 + 1)) = ∏ a ∈ Finset.Icc (1 : ℕ) 2015, F a := by
    apply Finset.prod_bij (fun a _ ↦ a.1 + 1)
    · intro a _
      exact Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 a.1, a.isLt⟩
    · intro a₁ _ a₂ _ h
      exact Fin.ext (Nat.add_right_cancel h)
    · intro b hb
      have hb' := Finset.mem_Icc.mp hb
      let a : Fin 2015 := ⟨b - 1, by omega⟩ -- non-rewrite step
      refine ⟨a, Finset.mem_univ a, ?_⟩
      exact Nat.sub_add_cancel hb'.1
    · intro a _
      congr 1
      norm_cast
  have hindex : P = Q := by
    let F : ℂ → ℂ := fun n ↦ ∏ b : Fin 2015,
      (1 + Complex.exp (2 * Real.pi * Complex.I * n * (b.1 + 1) / 2015))
    dsimp only [P]
    change (∏ a : Fin 2015, F (a.1 + 1)) = Q
    rw [hindex_one F]
    dsimp [F, Q]
    apply Finset.prod_congr rfl
    intro a ha
    let G : ℂ → ℂ := fun n ↦
      (1 + Complex.exp (2 * Real.pi * Complex.I * a * n / 2015))
    change (∏ b : Fin 2015, G (b.1 + 1)) =
      ∏ b ∈ Finset.Icc (1 : ℕ) 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))
    rw [hindex_one G]
    dsimp [G]
    apply Finset.prod_congr rfl
    intro b hb
    congr 2
    ring -- non-rewrite step
  have hinner (a : Fin 2015) :
      (starRingEnd ℂ) (∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
        ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)) := by
    let z : Fin 2015 → ℂ := fun b ↦
      Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)
    have hzconj (b : Fin 2015) : (starRingEnd ℂ) (z b) = (z b)⁻¹ := by
      rw [← Complex.exp_neg]
      dsimp [z]
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_div₀, map_mul, map_add, map_one, map_ofNat, map_natCast,
        Complex.conj_ofReal, Complex.conj_I]
      ring -- non-rewrite step
    have hterm (b : Fin 2015) : 1 + (z b)⁻¹ = (z b)⁻¹ * (1 + z b) := by
      rw [mul_add, inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one, add_comm]
    have hzprod : (∏ b : Fin 2015, z b) = 1 := by
      dsimp [z]
      rw [← Complex.exp_sum]
      have hsum :
          (∑ b : Fin 2015,
            (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015 : ℂ)) =
            (((a.1 + 1) * 1008 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun b : ℕ ↦
            (2 * Real.pi * Complex.I * (a.1 + 1) * (b + 1) / 2015 : ℂ)) 2015]
        push_cast
        simp_rw [show ∀ b : ℕ,
          (2 * Real.pi * Complex.I * (a.1 + 1) * (b + 1) / 2015 : ℂ) =
            (2 * Real.pi * Complex.I * (a.1 + 1) / 2015) * (b + 1) by
              intro b
              ring]
        rw [← Finset.mul_sum]
        norm_num [Finset.sum_add_distrib, Finset.sum_range_id] -- non-rewrite step
        ring -- non-rewrite step
      rw [hsum, Complex.exp_int_mul_two_pi_mul_I]
    change (starRingEnd ℂ) (∏ b : Fin 2015, (1 + z b)) =
      ∏ b : Fin 2015, (1 + z b)
    rw [map_prod]
    simp_rw [map_add, map_one, hzconj, hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hzprod]
    simp only [inv_one, one_mul]
  have hreal : (P.re : ℂ) = P := by
    apply Complex.conj_eq_iff_re.mp
    dsimp [P]
    rw [map_prod]
    simp_rw [hinner]
  have hlog2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  change Complex.log P / Complex.log (2 : ℂ) = (13725 : ℂ)
  rw [← hreal, hindex, hlog2]
  exact problem_statement_assumed
