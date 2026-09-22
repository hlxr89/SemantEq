import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬ ∃ k : ℤ, k^2 = n^3 + a * n^2 + b * n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  let d : ℤ := |a| + |b| + |c| + 1
  obtain ⟨t, ht, htnsq⟩ := dummy_assumed
    (3 * d + a) (3 * d^2 + 2 * a * d + b) (d^3 + a * d^2 + b * d + c)
  let n : ℤ := (t : ℤ) + d
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hn : 0 < n := by
    dsimp [n]
    omega
  have haa : 0 ≤ |a| := abs_nonneg a
  have hba : 0 ≤ |b| := abs_nonneg b
  have hca : 0 ≤ |c| := abs_nonneg c
  have ha : -d < a ∧ a < d := by
    have ha₁ : a ≤ |a| := le_abs_self a
    have ha₂ : -a ≤ |a| := neg_le_abs a
    dsimp [d]
    constructor <;> omega
  have hb : -d < b ∧ b < d := by
    have hb₁ : b ≤ |b| := le_abs_self b
    have hb₂ : -b ≤ |b| := neg_le_abs b
    dsimp [d]
    constructor <;> omega
  have hc : -d < c ∧ c < d := by
    have hc₁ : c ≤ |c| := le_abs_self c
    have hc₂ : -c ≤ |c| := neg_le_abs c
    dsimp [d]
    constructor <;> omega
  have hpoly : 0 < n^3 + a*n^2 + b*n + c := by
    have hdn : d < n := by
      dsimp [n]
      have : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
      omega
    nlinarith [sq_nonneg (n + a), sq_nonneg (n + b)]
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply htnsq
  refine ⟨m, ?_⟩
  have hm_sq : (m : ℝ)^2 =
      (n : ℝ)^3 + (a : ℝ)*(n : ℝ)^2 + (b : ℝ)*(n : ℝ) + (c : ℝ) := by
    rw [← hm]
    exact Real.sq_sqrt (by exact_mod_cast hpoly.le)
  have hm_sq_int : m^2 = n^3 + a*n^2 + b*n + c := by
    exact_mod_cast hm_sq
  dsimp [n] at hm_sq_int
  norm_num at hm_sq_int ⊢
  nlinarith
