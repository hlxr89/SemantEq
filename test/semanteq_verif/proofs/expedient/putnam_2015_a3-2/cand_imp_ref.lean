import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * ((a * b : ℂ) / (2015 : ℂ))))).re) / Real.log 2 = 13725 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution :=
by
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
  let e : Fin 2015 → Fin 2015 := fun b =>
    if h : b.1 = 2014 then b else ⟨2013 - b.1, by omega⟩
  have he : ∀ b, e (e b) = b := by
    intro b
    by_cases h : b.1 = 2014
    · simp [e, h]
    · have hb : b.1 ≤ 2013 := by omega
      have h2 : 2013 - b.1 ≠ 2014 := by omega
      simp [e, h, h2]
      apply Fin.ext
      change 2013 - (2013 - b.1) = b.1
      omega
  let E : Fin 2015 ≃ Fin 2015 :=
    { toFun := e
      invFun := e
      left_inv := he
      right_inv := he }
  have hfactor (a b : Fin 2015) :
      (starRingEnd ℂ) (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)) =
      1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * ((e b).1 + 1) / 2015) := by
    rw [map_add, map_one, ← Complex.exp_conj]
    simp only [map_mul, map_div₀, map_add, map_natCast, map_ofNat,
      Complex.conj_I, Complex.conj_ofReal]
    congr 1
    apply (Complex.exp_eq_exp_iff_exists_int).2
    by_cases h : b.1 = 2014
    · refine ⟨-2 * (a.1 + 1), ?_⟩
      simp [e, h]
      push_cast
      ring
    · have hb : b.1 ≤ 2013 := by omega
      refine ⟨-(a.1 + 1), ?_⟩
      simp [e, h]
      rw [Nat.cast_sub hb]
      field_simp
      ring
  have hinner (a : Fin 2015) :
      (starRingEnd ℂ) (∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)) := by
    rw [map_prod]
    calc
      (∏ b : Fin 2015, (starRingEnd ℂ) (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
          ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * ((e b).1 + 1) / 2015)) := by
            apply Finset.prod_congr rfl
            intro b hb
            exact hfactor a b
      _ = _ := Equiv.prod_comp E (fun b : Fin 2015 =>
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)))
  have hpconj : (starRingEnd ℂ) P = P := by
    change (starRingEnd ℂ) (∏ a : Fin 2015, ∏ b : Fin 2015,
      (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro a ha
    exact hinner a
  have hreal : (P.re : ℂ) = P := Complex.conj_eq_iff_re.mp hpconj
  have h := problem_statement_assumed
  rw [hprod] at h
  change Complex.log (P.re : ℂ) / (Real.log 2 : ℂ) = (13725 : ℂ) at h
  rw [hreal, Complex.ofReal_log (show (0 : ℝ) ≤ 2 by norm_num)] at h
  exact h
