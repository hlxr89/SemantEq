import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ (n : ℕ), ¬ ∃ (m : ℤ), m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let T : ℤ := |a| + |b| + |c| + 1
  obtain ⟨k, hk⟩ := dummy_assumed
    (a + 3 * T)
    (b + 2 * a * T + 3 * T ^ 2)
    (c + b * T + a * T ^ 2 + T ^ 3)
  let n : ℤ := (k : ℤ) + T
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hn : 0 < n := by
    dsimp [n]
    omega
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply hk
  refine ⟨m, ?_⟩
  have ha : -|a| ≤ a := (abs_le.mp (le_refl |a|)).1
  have hb : -|b| ≤ b := (abs_le.mp (le_refl |b|)).1
  have hc : -|c| ≤ c := (abs_le.mp (le_refl |c|)).1
  have hknonneg : (0 : ℤ) ≤ k := by omega
  have hnT : T ≤ n := by
    dsimp [n]
    omega
  have hn1 : 1 ≤ n := by omega
  have hna : |a| ≤ n := by
    have habs : 0 ≤ |b| := abs_nonneg b
    have hacs : 0 ≤ |c| := abs_nonneg c
    dsimp [T] at hnT
    omega
  have hPpos : 0 < n ^ 3 + a * n ^ 2 + b * n + c := by
    have hnb : 0 ≤ |b| := abs_nonneg b
    have hnc : 0 ≤ |c| := abs_nonneg c
    have hn0 : 0 ≤ n := le_of_lt hn
    have h1 : 0 ≤ n ^ 2 * (n - |a|) := mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hna)
    have h2 : 0 ≤ |b| * n * (n - 1) :=
      mul_nonneg (mul_nonneg hnb hn0) (sub_nonneg.mpr hn1)
    have h3 : 0 ≤ |c| * (n ^ 2 - 1) :=
      mul_nonneg hnc (by nlinarith [sq_nonneg (n - 1)])
    dsimp [T] at hnT
    nlinarith
  have hsquare : (m : ℝ) ^ 2 =
      (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * (n : ℝ) + (c : ℝ) := by
    rw [← hm]
    exact Real.sq_sqrt (by exact_mod_cast (le_of_lt hPpos))
  have hsquareZ : m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    exact_mod_cast hsquare
  rw [hsquareZ]
  ring
