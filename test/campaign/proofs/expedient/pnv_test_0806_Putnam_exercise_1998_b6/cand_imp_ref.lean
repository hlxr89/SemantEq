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
  let K : ℤ := |a| + |b| + |c| + 1
  obtain ⟨n, hn⟩ := dummy_assumed (3 * K + a)
    (3 * K^2 + 2 * a * K + b) (K^3 + a * K^2 + b * K + c)
  refine ⟨(n : ℤ) + K, ?_, ?_⟩
  · dsimp [K]
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    positivity
  rintro ⟨m, hm⟩
  apply hn
  refine ⟨m, ?_⟩
  let x : ℤ := (n : ℤ) + K
  have hx : 1 ≤ x := by
    dsimp [x, K]
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    omega
  have hxa : 1 ≤ x + a := by
    dsimp [x, K]
    have ha := neg_abs_le a
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    omega
  have hxb : 1 ≤ x + b := by
    dsimp [x, K]
    have ha := abs_nonneg a
    have hb := neg_abs_le b
    have hc := abs_nonneg c
    omega
  have hxc : 1 ≤ x + c := by
    dsimp [x, K]
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hc := neg_abs_le c
    omega
  have ht : x^2 ≤ x^2 * (x + a) := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x + a - 1 by omega)]
  have hu : x ≤ x * (x + b) := by
    nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ x + b - 1 by omega)]
  have hp : 0 ≤ x^3 + a*x^2 + b*x + c := by
    nlinarith
  have hm' : Real.sqrt (x^3 + a*x^2 + b*x + c) = (m : ℝ) := by
    simpa [x] using hm
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (x^3 + a*x^2 + b*x + c : ℤ) by exact_mod_cast hp)
  have heq : m^2 = x^3 + a*x^2 + b*x + c := by
    exact_mod_cast (show (m : ℝ)^2 = (x^3 + a*x^2 + b*x + c : ℤ) by
      rw [← hm']
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using hs)
  convert heq using 1 <;> dsimp [x] <;> ring
