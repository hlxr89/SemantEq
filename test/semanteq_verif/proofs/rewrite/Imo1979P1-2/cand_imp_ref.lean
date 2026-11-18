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
  obtain ⟨a, b, ha, hb, hS, hab, hdvd⟩ := problem_statement_assumed
  have hp_abs : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg (le_of_lt hp)
  have hq_abs : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg (le_of_lt hq)
  have hp_cast : (p.natAbs : ℚ) = (p : ℚ) := by
    change (((p.natAbs : ℕ) : ℤ) : ℚ) = (p : ℚ)
    rw [hp_abs]
  have hq_cast : (q.natAbs : ℚ) = (q : ℚ) := by
    change (((q.natAbs : ℕ) : ℤ) : ℚ) = (q : ℚ)
    rw [hq_abs]
  have hrat : (p.natAbs : ℚ) / q.natAbs = (a : ℚ) / b := by
    rw [hp_cast, hq_cast, ← hS, S, ← h]
  have hcrossQ : (p.natAbs : ℚ) * b = a * q.natAbs := by
    exact (div_eq_div_iff (by positivity) (by positivity)).mp hrat
  have hcross : p.natAbs * b = a * q.natAbs := by
    exact_mod_cast hcrossQ
  have ha_dvd : a ∣ p.natAbs := by
    apply (Nat.coprime_iff_gcd_eq_one.mpr hab).dvd_of_dvd_mul_right
    exact ⟨q.natAbs, hcross⟩
  have h1979_nat : 1979 ∣ p.natAbs := dvd_trans hdvd ha_dvd
  have h1979_int : (1979 : ℤ) ∣ (p.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr h1979_nat
  rw [hp_abs] at h1979_int
  exact h1979_int
