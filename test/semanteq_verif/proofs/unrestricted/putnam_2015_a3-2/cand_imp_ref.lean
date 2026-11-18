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
  have hQim : Q.im = 0 := by
    let S := {n : ℕ // n ∈ Finset.Icc 1 2015}
    letI : Fintype S := Fintype.ofFinset (Finset.Icc 1 2015) (fun _ => Iff.rfl)
    let flip : S → S := fun a =>
      if h : a.1 = 2015 then a else
        ⟨2015 - a.1, by
          have ha := a.property
          simp only [Finset.mem_Icc] at ha ⊢
          omega⟩
    have hflip : Function.Involutive flip := by
      intro a
      have ha := a.property
      simp only [Finset.mem_Icc] at ha
      by_cases h : a.1 = 2015
      · simp [flip, h]
      · have hne : 2015 - a.1 ≠ 2015 := by omega
        simp [flip, h, hne]
        apply Subtype.ext
        simp
        omega
    let j : Equiv.Perm S := hflip.toPerm
    have hs2 : star (2 : ℂ) = 2 := star_natCast 2
    have hs2015 : star (2015 : ℂ) = 2015 := star_natCast 2015
    apply Complex.conj_eq_iff_im.mp
    change star Q = Q
    have hQ : Q = ∏ a : S, ∏ b : S,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (((a.1 * b.1 : ℕ) : ℂ) / (2015 : ℂ)))) := by
      dsimp [Q]
      rw [Finset.prod_subtype (p := fun x => x ∈ Finset.Icc 1 2015) _ (by simp)]
      apply Fintype.prod_congr
      intro a
      rw [Finset.prod_subtype (p := fun x => x ∈ Finset.Icc 1 2015) _ (by simp)]
      apply Fintype.prod_congr
      intro b
      set_option maxRecDepth 10000 in
        congr 2
      norm_cast
    rw [hQ, Complex.star_def]
    simp only [map_prod, map_add, map_one]
    apply Fintype.prod_equiv j _ _
    intro a
    apply Fintype.prod_congr
    intro b
    set_option maxRecDepth 10000 in
      congr 2
    rw [← Complex.exp_conj]
    rw [Complex.exp_eq_exp_iff_exists_int]
    have ha := a.property
    simp only [Finset.mem_Icc] at ha
    by_cases h : a.1 = 2015
    · refine ⟨-(2 * (b.1 : ℤ)), ?_⟩
      simp [j, Function.Involutive.toPerm, flip, h]
      push_cast
      field_simp
      norm_num
      simp only [← Complex.star_def, hs2, hs2015]
      ring
    · refine ⟨-(b.1 : ℤ), ?_⟩
      have hlt : a.1 < 2015 := by omega
      simp [j, Function.Involutive.toPerm, flip, h, hlt]
      push_cast [Nat.cast_sub (by omega : a.1 ≤ 2015)]
      field_simp
      norm_num
      simp only [← Complex.star_def, hs2, hs2015]
      ring
  have hQre : (Q.re : ℂ) = Q := by
    apply Complex.ext
    · simp
    · simpa using hQim.symm
  have h := problem_statement_assumed
  change Complex.log (Q.re : ℂ) / (Real.log 2 : ℂ) = (13725 : ℂ) at h
  have hlog2eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2)).symm
  change Complex.log P / Complex.log 2 = (13725 : ℂ)
  rw [hPQ, ← hQre, hlog2eq]
  exact h
