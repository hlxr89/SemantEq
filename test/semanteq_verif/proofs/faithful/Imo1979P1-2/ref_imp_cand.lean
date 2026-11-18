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
  have hS : 0 < S := by native_decide
  have hnum : 0 < S.num := Rat.num_pos.mpr hS
  have hdiv : (1979 : ℤ) ∣ S.num :=
    imo1979_p1_assumed S.num S.den hnum (by exact_mod_cast S.den_pos)
      (by
        change (S.num : ℚ) / (S.den : ℚ) = S
        exact S.num_div_den)
  refine ⟨S.num.natAbs, S.den, ?_, S.den_pos, ?_, S.reduced.gcd_eq_one, ?_⟩
  · exact Int.natAbs_pos.mpr (ne_of_gt hnum)
  · have hcast : (S.num.natAbs : ℚ) = (S.num : ℚ) := by
      calc
        (S.num.natAbs : ℚ) = ((S.num.natAbs : ℤ) : ℚ) :=
          (Int.cast_natCast S.num.natAbs).symm
        _ = (S.num : ℚ) :=
          congrArg (fun z : ℤ => (z : ℚ))
            (Int.natAbs_of_nonneg (le_of_lt hnum))
    rw [hcast]
    exact S.num_div_den.symm
  · exact Int.natCast_dvd.mp hdiv
