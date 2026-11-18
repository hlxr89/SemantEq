import Mathlib

open Complex Real

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2015_a3_solution : ℂ := 13725

-- ===== assumed statement (antecedent) =====
theorem putnam_2015_a3_assumed :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = putnam_2015_a3_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  (Complex.log (Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a => Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b => (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015))) / Real.log 2 : ℂ) = (13725 : ℂ) := by
  have hshift (f : ℂ → ℂ) :
      (∏ i : Fin 2015, f (i.1 + 1)) =
        ∏ i ∈ Finset.Icc (1 : ℕ) 2015, f i := by
    apply Finset.prod_bij (fun i _ => i.1 + 1)
    · intro i hi
      exact Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le _),
        Nat.lt_iff_add_one_le.mp i.isLt⟩
    · intro a ha b hb hab
      apply Fin.ext
      exact Nat.add_right_cancel hab
    · intro b hb
      have hb' := Finset.mem_Icc.mp hb
      let i : Fin 2015 :=
        ⟨b - 1, lt_of_lt_of_le (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hb'.1)
          Nat.zero_lt_one) hb'.2⟩
      exact ⟨i, Finset.mem_univ i, Nat.sub_add_cancel hb'.1⟩
    · intro i hi
      apply congrArg f
      rw [Nat.cast_add, Nat.cast_one]
  have hprod :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
      Finset.prod (Finset.Icc (1 : ℕ) 2015) fun a =>
        Finset.prod (Finset.Icc (1 : ℕ) 2015) fun b =>
          (1 + Complex.exp (2 * Real.pi * Complex.I * (a * b : ℂ) / 2015)) := by
    rw [hshift (fun x => ∏ b : Fin 2015,
      (1 + Complex.exp (2 * Real.pi * Complex.I * x * (b.1 + 1) / 2015)))]
    apply Finset.prod_congr rfl
    intro a ha
    rw [hshift (fun x =>
      (1 + Complex.exp (2 * Real.pi * Complex.I * a * x / 2015)))]
    simp only [mul_assoc]
  have h := putnam_2015_a3_assumed
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log zero_le_two).symm
  rw [hprod, hlog] at h
  exact h
