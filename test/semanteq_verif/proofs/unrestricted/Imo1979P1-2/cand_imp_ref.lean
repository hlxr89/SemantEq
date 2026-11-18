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
  obtain ⟨p₀, q₀, hp₀, hq₀, hs, hgcd, hd⟩ := problem_statement_assumed
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hq₀Q : (q₀ : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq₀)
  have heq : (p : ℚ) / (q : ℚ) = (p₀ : ℚ) / (q₀ : ℚ) := by
    calc
      (p : ℚ) / (q : ℚ) = S := by simpa [S] using h
      _ = (p₀ : ℚ) / (q₀ : ℚ) := hs
  have hcrossQ : (p : ℚ) * (q₀ : ℚ) = (p₀ : ℚ) * (q : ℚ) :=
    (div_eq_div_iff hqQ hq₀Q).mp heq
  have hcrossZ : p * (q₀ : ℤ) = (p₀ : ℤ) * q := by
    exact_mod_cast hcrossQ
  have hcrossN : p.natAbs * q₀ = p₀ * q.natAbs := by
    have := congrArg Int.natAbs hcrossZ
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using this
  have hpq : p₀.Coprime q₀ := Nat.coprime_iff_gcd_eq_one.mpr hgcd
  have hc : Nat.Coprime 1979 q₀ := Nat.Coprime.of_dvd_left hd hpq
  have hprod : 1979 ∣ p.natAbs * q₀ := by
    rw [hcrossN]
    exact dvd_mul_of_dvd_left hd q.natAbs
  have hpabs : 1979 ∣ p.natAbs := hc.dvd_of_dvd_mul_right hprod
  have hpcast : (p.natAbs : ℤ) = p := by
    rw [Int.natCast_natAbs, abs_of_pos hp]
  rw [← hpcast]
  exact_mod_cast hpabs
