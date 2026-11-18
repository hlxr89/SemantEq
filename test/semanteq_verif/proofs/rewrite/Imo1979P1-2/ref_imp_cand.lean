import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def S : ℚ := Finset.sum (Finset.range 1319) (fun k => ((-1 : ℚ) ^ k) / (k + 1 : ℚ))

-- ===== assumed statement (antecedent) =====
theorem imo1979_p1_assumed (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ S = (p : ℚ) / (q : ℚ) ∧ Nat.gcd p q = 1 ∧ 1979 ∣ p := by
  have hSpos : 0 < S := by
    norm_num [S, Finset.sum_range_succ] -- non-rewrite step
  have hnum : 0 < S.num := Rat.num_pos.mpr hSpos
  have hden : 0 < S.den := S.den_pos
  have habsZ : (S.num.natAbs : ℤ) = S.num :=
    Int.natAbs_of_nonneg (le_of_lt hnum)
  have habsQ : (S.num.natAbs : ℚ) = (S.num : ℚ) := by
    change (((S.num.natAbs : ℕ) : ℤ) : ℚ) = (S.num : ℚ)
    rw [habsZ]
  have hratio : (S.num : ℚ) / S.den =
      ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1) := by
    rw [Rat.num_div_den, ← S]
  have hdvdZ : (1979 : ℤ) ∣ S.num :=
    imo1979_p1_assumed S.num S.den hnum (by exact_mod_cast hden) hratio
  refine ⟨S.num.natAbs, S.den, ?_, hden, ?_, ?_, ?_⟩
  · exact Int.natAbs_pos.mpr (ne_of_gt hnum)
  · rw [habsQ, Rat.num_div_den]
  · exact Nat.coprime_iff_gcd_eq_one.mp S.reduced
  · exact Int.natCast_dvd.mp hdvdZ
