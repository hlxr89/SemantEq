import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1979_p1_assumed (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ 
  (p : ℚ) / q = Finset.sum (Finset.range 1319) (fun k => ((-1 : ℚ)^k * (1 : ℚ) / (k + 1 : ℚ))) ∧
  1979 ∣ p := by
  let r : ℚ := Finset.sum (Finset.range 1319)
    (fun k => ((-1 : ℚ)^k * (1 : ℚ) / (k + 1 : ℚ)))
  have hr : 0 < r := by native_decide
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have hd : 0 < (r.den : ℤ) := by exact_mod_cast r.den_pos
  have heq : (r.num : ℚ) / r.den =
      ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1) := by
    rw [Rat.num_div_den]
    simp [r]
  have hdiv : 1979 ∣ r.num := imo1979_p1_assumed r.num r.den hn hd heq
  have hnum : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg (le_of_lt hn)
  have hnumQ : (r.num.natAbs : ℚ) = (r.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hnum
  refine ⟨r.num.natAbs, r.den, ?_, r.den_pos, ?_, ?_⟩
  · exact Int.natAbs_pos.mpr (ne_of_gt hn)
  · calc
      (r.num.natAbs : ℚ) / r.den = (r.num : ℚ) / r.den :=
        congrArg (fun x : ℚ => x / r.den) hnumQ
      _ = r := Rat.num_div_den r
      _ = _ := rfl
  · rw [← hnum] at hdiv
    exact Int.natCast_dvd_natCast.mp hdiv
