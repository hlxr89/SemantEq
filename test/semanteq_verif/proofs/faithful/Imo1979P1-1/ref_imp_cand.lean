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
  have hs : 0 < s := by native_decide
  have hdenQ : 0 < (s.den : ℚ) := by exact_mod_cast s.den_pos
  have hs' : 0 < (s.num : ℚ) / (s.den : ℚ) := by
    simpa only [s.num_div_den] using hs
  have hnumQ : 0 < (s.num : ℚ) := by
    rcases (div_pos_iff.mp hs') with h | h
    · exact h.1
    · exfalso
      exact (not_lt_of_ge (le_of_lt hdenQ)) h.2
  have hnum : 0 < s.num := by exact_mod_cast hnumQ
  have hden : 0 < (s.den : ℤ) := by exact_mod_cast s.den_pos
  have hdZ : (1979 : ℤ) ∣ s.num := by
    apply imo1979_p1_assumed s.num s.den hnum hden
    exact s.num_div_den
  have hto : (s.num.toNat : ℤ) = s.num :=
    Int.toNat_of_nonneg (le_of_lt hnum)
  have hp : 0 < s.num.toNat := by omega
  have hcast : ((s.num.toNat : ℕ) : ℚ) = (s.num : ℚ) := by
    exact_mod_cast hto
  refine ⟨s.num.toNat, s.den, hp, s.den_pos, ?_, ?_⟩
  · rw [hcast, s.num_div_den]
    simp only [s, mul_one]
  · apply Int.ofNat_dvd.mp
    rw [hto]
    exact hdZ
