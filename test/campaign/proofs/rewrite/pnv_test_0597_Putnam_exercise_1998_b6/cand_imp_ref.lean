import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b c : ℤ} : ∃ n : ℕ, ¬ ∃ m : ℤ, m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let k : ℤ := |a| + |b| + |c| + 1
  have hk : 0 < k := by
    dsimp [k]
    positivity
  obtain ⟨r, hr⟩ := dummy_assumed
    (a := a + 3 * k)
    (b := b + 2 * a * k + 3 * k ^ 2)
    (c := c + b * k + a * k ^ 2 + k ^ 3)
  let n : ℤ := r + k
  have hn : 0 < n := by
    dsimp [n]
    exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg r) hk
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply hr
  refine ⟨m, ?_⟩
  have hkn : k ≤ n := by
    dsimp [n]
    exact le_add_of_nonneg_left (Int.natCast_nonneg r)
  have hn1 : 1 ≤ n := by omega
  have hn_sq : n ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
  have hdom : 0 ≤ (n - k) * n ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hkn) (sq_nonneg n)
  have ha : 0 ≤ (a + |a|) * n ^ 2 :=
    mul_nonneg (by exact neg_le_iff_add_nonneg.mp (neg_abs_le a)) (sq_nonneg n)
  have hb : 0 ≤ (b + |b|) * n :=
    mul_nonneg (by exact neg_le_iff_add_nonneg.mp (neg_abs_le b)) (le_of_lt hn)
  have hpoly : 0 ≤ n ^ 3 + a * n ^ 2 + b * n + c := by
    dsimp [k] at hdom
    nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, neg_abs_le c] -- non-rewrite step
  have hsq : (m : ℝ) ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    rw [← hm]
    exact Real.sq_sqrt (by exact_mod_cast hpoly)
  have hsq_int : m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    exact_mod_cast hsq
  dsimp [n] at hsq_int
  rw [hsq_int]
  ring -- non-rewrite step
