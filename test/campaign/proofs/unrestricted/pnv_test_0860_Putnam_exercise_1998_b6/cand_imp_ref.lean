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
  have hfinite : ∀ a b c : ZMod 4, ∃ r : ZMod 4, ∀ m : ZMod 4,
      r ^ 3 + a * r ^ 2 + b * r + c ≠ m ^ 2 := by
    native_decide
  obtain ⟨r, hr⟩ := hfinite (a : ZMod 4) (b : ZMod 4) (c : ZMod 4)
  let A : ℤ := |a|
  let B : ℤ := |b|
  let C : ℤ := |c|
  let n : ℤ := 4 * (A + B + C + 1) + (r.val : ℤ)
  have hA : 0 ≤ A := by simp [A]
  have hB : 0 ≤ B := by simp [B]
  have hC : 0 ≤ C := by simp [C]
  have ha : -A ≤ a := by simpa [A] using neg_abs_le a
  have hb : -B ≤ b := by simpa [B] using neg_abs_le b
  have hc : -C ≤ c := by simpa [C] using neg_abs_le c
  have hrval : 0 ≤ (r.val : ℤ) := by positivity
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hnlarge : A + B + C < n := by
    dsimp [n]
    omega
  have hn_sq : n ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
  have hone_sq : 1 ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
  have hBn : B * n ≤ B * n ^ 2 :=
    mul_le_mul_of_nonneg_left hn_sq hB
  have hCone : C ≤ C * n ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_left hone_sq hC
  have hcore : 0 < n ^ 2 * (n - A - B - C) := by
    exact mul_pos (sq_pos_of_pos hn) (by omega)
  have hp : 0 < n ^ 3 + a * n ^ 2 + b * n + c := by
    have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
    have hbn : 0 ≤ n := hn.le
    have ha' := mul_le_mul_of_nonneg_right ha hn2
    have hb' := mul_le_mul_of_nonneg_right hb hbn
    nlinarith
  have hncast : (n : ZMod 4) = r := by
    dsimp [n]
    rw [Int.cast_add, Int.cast_mul,
      show ((4 : ℤ) : ZMod 4) = 0 by decide, zero_mul, zero_add,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have hnsq : ¬ ∃ m : ℤ, n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
    rintro ⟨m, hm⟩
    apply hr (m : ZMod 4)
    have hm' := congrArg (fun z : ℤ => (z : ZMod 4)) hm
    simpa [hncast] using hm'
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply hnsq
  refine ⟨m, ?_⟩
  have hp' : (0 : ℝ) ≤ (n ^ 3 + a * n ^ 2 + b * n + c : ℤ) := by
    exact_mod_cast hp.le
  norm_num only [Int.cast_add, Int.cast_mul, Int.cast_pow] at hp'
  have hm' := congrArg (fun x : ℝ => x ^ 2) hm
  dsimp at hm'
  rw [Real.sq_sqrt hp'] at hm'
  exact_mod_cast hm'
