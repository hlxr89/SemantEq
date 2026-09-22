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
  let k : ℤ := |a| + |b| + |c| + 1
  obtain ⟨n, hn, hnot⟩ := dummy_assumed
    (3 * k + a) (3 * k ^ 2 + 2 * a * k + b)
    (k ^ 3 + a * k ^ 2 + b * k + c)
  refine ⟨n + k, ?_, ?_⟩
  · dsimp [k]
    have ha0 := abs_nonneg a
    have hb0 := abs_nonneg b
    have hc0 := abs_nonneg c
    omega -- non-rewrite step
  · rintro ⟨m, hm⟩
    apply hnot
    refine ⟨m, ?_⟩
    have hN : 0 < n + k := by
      dsimp [k]
      have ha0 := abs_nonneg a
      have hb0 := abs_nonneg b
      have hc0 := abs_nonneg c
      omega -- non-rewrite step
    have hN0 : 0 ≤ n + k := le_of_lt hN
    have hNa : 1 ≤ n + k - |a| := by
      dsimp [k]
      have hb0 := abs_nonneg b
      have hc0 := abs_nonneg c
      omega -- non-rewrite step
    have hNb : 1 ≤ n + k - |b| := by
      dsimp [k]
      have ha0 := abs_nonneg a
      have hc0 := abs_nonneg c
      omega -- non-rewrite step
    have hNc : 1 ≤ n + k - |c| := by
      dsimp [k]
      have ha0 := abs_nonneg a
      have hb0 := abs_nonneg b
      omega -- non-rewrite step
    have hN2 : 0 ≤ (n + k) ^ 2 := sq_nonneg (n + k)
    have hAprod :
        (n + k) ^ 2 ≤ (n + k) ^ 2 * (n + k - |a|) := by
      simpa using mul_le_mul_of_nonneg_left hNa hN2
    have hBprod : n + k ≤ (n + k) * (n + k - |b|) := by
      simpa using mul_le_mul_of_nonneg_left hNb hN0
    have haMul : -|a| * (n + k) ^ 2 ≤ a * (n + k) ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_abs_le a) hN2
    have hbMul : -|b| * (n + k) ≤ b * (n + k) :=
      mul_le_mul_of_nonneg_right (neg_abs_le b) hN0
    have hpoly :
        0 ≤ (n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c := by
      nlinarith [neg_abs_le c, hAprod, hBprod, haMul, hbMul, hNc] -- non-rewrite step
    have hpolyR :
        (0 : ℝ) ≤
          (n + k : ℤ) ^ 3 + a * (n + k : ℤ) ^ 2 + b * (n + k : ℤ) + c := by
      exact_mod_cast hpoly
    have hsquare := congrArg (fun x : ℝ => x ^ 2) hm
    dsimp only at hsquare
    rw [Real.sq_sqrt hpolyR] at hsquare
    have hsquareInt :
        (n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c = m ^ 2 := by
      exact_mod_cast hsquare
    rw [show
      n ^ 3 + (3 * k + a) * n ^ 2 +
          (3 * k ^ 2 + 2 * a * k + b) * n +
          (k ^ 3 + a * k ^ 2 + b * k + c) =
        (n + k) ^ 3 + a * (n + k) ^ 2 + b * (n + k) + c by
          ring] -- non-rewrite step
    exact hsquareInt
