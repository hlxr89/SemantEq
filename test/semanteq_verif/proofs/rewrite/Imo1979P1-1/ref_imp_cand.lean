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
  let s : ℚ := ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)
  have hs : 0 < s := by
    dsimp [s]
    positivity -- non-rewrite step
  have hnum : 0 < s.num := Rat.num_pos.mpr hs
  have hnat : (s.num.natAbs : ℤ) = s.num := Int.natAbs_of_nonneg hnum.le
  have hdivZ : (1979 : ℤ) ∣ s.num := by
    apply imo1979_p1_assumed s.num s.den hnum
    · exact_mod_cast s.den_pos
    · exact Rat.num_div_den s
  have hdivN : 1979 ∣ s.num.natAbs := by
    rw [← hnat] at hdivZ
    exact_mod_cast hdivZ
  refine ⟨s.num.natAbs, s.den, ?_, s.den_pos, ?_, hdivN⟩
  · exact Int.natAbs_pos.mpr hnum.ne'
  · have hcast : (s.num.natAbs : ℚ) = s.num := by
      exact congrArg (fun z : ℤ => (z : ℚ)) hnat
    rw [hcast]
    simpa only [s, mul_one] using Rat.num_div_den s
