import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ (n : ℤ) (H : n > 0), ¬(∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c|
  obtain ⟨n, hn, hnot⟩ := dummy_assumed
    (3 * k + a)
    (3 * k ^ 2 + 2 * a * k + b)
    (k ^ 3 + a * k ^ 2 + b * k + c)
  refine ⟨n + k, ?_, ?_⟩
  · dsimp [k]
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : 0 ≤ |b| := abs_nonneg b
    have hc : 0 ≤ |c| := abs_nonneg c
    omega
  · rintro ⟨m, hm⟩
    apply hnot
    refine ⟨m, ?_⟩
    have ha : -|a| ≤ a := neg_abs_le a
    have hb : -|b| ≤ b := neg_abs_le b
    have hc : -|c| ≤ c := neg_abs_le c
    have hk : 0 ≤ k := by
      dsimp [k]
      positivity
    have hN : 0 < n + k := by omega
    have hNa : |a| < n + k := by
      dsimp [k] at *
      have hb0 : 0 ≤ |b| := abs_nonneg b
      have hc0 : 0 ≤ |c| := abs_nonneg c
      omega
    have hP : 0 ≤ (n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c := by
      have hN0 : 0 ≤ n + k := le_of_lt hN
      have hN1 : 1 ≤ n + k := by omega
      have hN_sq_ge_N : n + k ≤ (n + k) ^ 2 := by nlinarith
      have hN_sq : 0 ≤ (n + k) ^ 2 := sq_nonneg (n + k)
      have hA : 0 ≤ (n + k) ^ 2 * ((n + k) - |a|) :=
        mul_nonneg hN_sq (by omega)
      have hB : 0 ≤ |b| * ((n + k) ^ 2 - (n + k)) :=
        mul_nonneg (abs_nonneg b) (by omega)
      have hC : 0 ≤ |c| * ((n + k) ^ 2 - 1) :=
        mul_nonneg (abs_nonneg c) (by nlinarith)
      dsimp [k] at hNa
      nlinarith
    have hP_real : 0 ≤ (((n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c : ℤ) : ℝ) := by
      exact_mod_cast hP
    have hm' : Real.sqrt (((n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c : ℤ) : ℝ) =
        (m : ℝ) := by
      convert hm using 1 <;> push_cast <;> ring
    have hsq : (Real.sqrt (((n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c : ℤ) : ℝ)) ^ 2 =
        ((n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c : ℤ) := by
      exact Real.sq_sqrt hP_real
    have hm_sq : ((n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c : ℤ) = m ^ 2 := by
      apply_mod_cast (show
        (((n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c : ℤ) : ℝ) = (m : ℝ) ^ 2 by
          rw [← hsq, hm'])
    calc
      n ^ 3 + (3 * k + a) * n ^ 2 + (3 * k ^ 2 + 2 * a * k + b) * n +
          (k ^ 3 + a * k ^ 2 + b * k + c) =
          (n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c := by ring
      _ = m ^ 2 := hm_sq
