import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def S : ℚ := Finset.sum (Finset.range 1319) (fun k => ((-1 : ℚ) ^ k) / (k + 1 : ℚ))

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ S = (p : ℚ) / (q : ℚ) ∧ Nat.gcd p q = 1 ∧ 1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  obtain ⟨a, b, ha, hb, hab, hgcd, h1979⟩ := problem_statement_assumed
  have heq : (p : ℚ) / q = (a : ℚ) / (b : ℚ) := by
    calc
      (p : ℚ) / q = S := by simpa [S] using h
      _ = (a : ℚ) / (b : ℚ) := hab
  have hcrossQ : (p : ℚ) * (b : ℚ) = (a : ℚ) * (q : ℚ) :=
    (div_eq_div_iff (by exact_mod_cast ne_of_gt hq) (by exact_mod_cast ne_of_gt hb)).mp heq
  have hcrossZ : p * (b : ℤ) = (a : ℤ) * q := by exact_mod_cast hcrossQ
  have hpcoe : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg (le_of_lt hp)
  have hqcoe : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg (le_of_lt hq)
  rw [← hpcoe, ← hqcoe] at hcrossZ
  have hcrossN : p.natAbs * b = a * q.natAbs := by exact_mod_cast hcrossZ
  have hacoprime : a.Coprime b := Nat.coprime_iff_gcd_eq_one.mpr hgcd
  have hadiv : a ∣ p.natAbs * b := ⟨q.natAbs, hcrossN⟩
  have hap : a ∣ p.natAbs := hacoprime.dvd_of_dvd_mul_right hadiv
  exact Int.natCast_dvd.mpr (h1979.trans hap)
