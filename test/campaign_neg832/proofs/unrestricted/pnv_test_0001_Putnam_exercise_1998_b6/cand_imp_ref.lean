import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) : ∃ (n : ℕ) (H : 0 < n), √(n^3 + a*n^2 + b*n + c) ≠ n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  have hres : ∀ A B C : ZMod 4, ∃ R : ZMod 4,
      ∀ M : ZMod 4, R^3 + A*R^2 + B*R + C ≠ M^2 := by
    native_decide
  obtain ⟨R, hR⟩ := hres (a : ZMod 4) (b : ZMod 4) (c : ZMod 4)
  let K : ℤ := |a| + |b| + |c| + 1
  let n : ℤ := 4 * K + R.val
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hn : 0 < n := by
    dsimp [n]
    have hval : 0 ≤ (R.val : ℤ) := by positivity
    omega
  have hlarge : |a| + |b| + |c| < n := by
    dsimp [n, K]
    have hval : 0 ≤ (R.val : ℤ) := by positivity
    omega
  have hn1 : 1 ≤ n := by omega
  have ha : -|a| ≤ a := neg_abs_le a
  have hb : -|b| ≤ b := neg_abs_le b
  have hc : -|c| ≤ c := neg_abs_le c
  have hpoly : 0 ≤ n^3 + a*n^2 + b*n + c := by
    have hn0 : 0 ≤ n := le_of_lt hn
    have hn2 : 0 ≤ n^2 := sq_nonneg n
    have hbn : -|b| * n ≤ b * n := by nlinarith
    have han2 : -|a| * n^2 ≤ a * n^2 := by nlinarith
    have hc' : -|c| ≤ c := hc
    have hn_sq : n ≤ n^2 := by nlinarith [sq_nonneg (n - 1)]
    have hone_sq : 1 ≤ n^2 := by nlinarith [sq_nonneg (n - 1)]
    have hbscale : |b| * n ≤ |b| * n^2 := by
      exact mul_le_mul_of_nonneg_left hn_sq (abs_nonneg b)
    have hcscale : |c| ≤ |c| * n^2 := by
      simpa using mul_le_mul_of_nonneg_left hone_sq (abs_nonneg c)
    have hdom : 0 < (n - (|a| + |b| + |c|)) * n^2 :=
      mul_pos (sub_pos.mpr hlarge) (sq_pos_of_pos hn)
    nlinarith
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  have hsqrt_sq : (Real.sqrt (n^3 + a*n^2 + b*n + c))^2 =
      (n^3 + a*n^2 + b*n + c : ℝ) := by
    rw [Real.sq_sqrt]
    exact_mod_cast hpoly
  have hsq : n^3 + a*n^2 + b*n + c = m^2 := by
    rw [hm] at hsqrt_sq
    exact_mod_cast hsqrt_sq.symm
  apply hR (m : ZMod 4)
  have hncast : (n : ZMod 4) = R := by
    dsimp [n]
    push_cast
    have hfour : (4 : ZMod 4) = 0 := by decide
    simp [hfour]
  rw [← hncast]
  have hcasteq := congrArg (fun z : ℤ => (z : ZMod 4)) hsq
  push_cast at hcasteq
  exact hcasteq
