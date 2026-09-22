import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ (n : ℕ) (hn : 0 < n), ¬ ∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c| + 1
  let A : ℤ := 3 * k + a
  let B : ℤ := 3 * k ^ 2 + 2 * a * k + b
  let C : ℤ := k ^ 3 + a * k ^ 2 + b * k + c
  obtain ⟨x, hx, hns⟩ := dummy_assumed (a := A) (b := B) (c := C)
  let n : ℤ := x + k
  refine ⟨n, ?_, ?_⟩
  · dsimp [n, k]
    have ha0 : 0 ≤ |a| := abs_nonneg a
    have hb0 : 0 ≤ |b| := abs_nonneg b
    have hc0 : 0 ≤ |c| := abs_nonneg c
    omega
  · rintro ⟨m, hm⟩
    apply hns
    refine ⟨m, ?_⟩
    have hk : 0 < k := by
      dsimp [k]
      have ha0 : 0 ≤ |a| := abs_nonneg a
      have hb0 : 0 ≤ |b| := abs_nonneg b
      have hc0 : 0 ≤ |c| := abs_nonneg c
      omega
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hpa : 0 < n ^ 3 + a * n ^ 2 + b * n + c := by
      have ha0 : 0 ≤ |a| := abs_nonneg a
      have hb0 : 0 ≤ |b| := abs_nonneg b
      have hc0 : 0 ≤ |c| := abs_nonneg c
      have hna : 1 ≤ n + a := by
        have := neg_le_abs a
        dsimp [n, k]
        omega
      have hnbc : |b| + |c| < n := by
        dsimp [n, k]
        omega
      have hdiff : |c| + 1 ≤ n - |b| := by omega
      have hmul : n * (|c| + 1) ≤ n * (n - |b|) :=
        mul_le_mul_of_nonneg_left hdiff hn.le
      have hlarge : |c| < n * (n - |b|) := by nlinarith
      have hquad : 0 < n ^ 2 + b * n + c := by
        have hb := neg_abs_le b
        have hc := neg_abs_le c
        nlinarith
      have hcubic : n ^ 2 ≤ n ^ 2 * (n + a) :=
        by simpa using mul_le_mul_of_nonneg_left hna (sq_nonneg n)
      nlinarith
    have hsquare : n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
      have hp0 : (0 : ℝ) ≤ (n ^ 3 + a * n ^ 2 + b * n + c : ℤ) := by
        exact_mod_cast hpa.le
      have hsquareR : (n ^ 3 + a * n ^ 2 + b * n + c : ℝ) = (m : ℝ) ^ 2 := by
        rw [← hm]
        simpa using (Real.sq_sqrt hp0).symm
      exact_mod_cast hsquareR
    dsimp [A, B, C, n, k]
    dsimp [n] at hsquare
    convert hsquare using 1 <;> ring
