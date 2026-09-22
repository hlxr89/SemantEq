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
  let t : ℤ := |a| + |b| + |c| + 1
  obtain ⟨k, hk⟩ := dummy_assumed
    (3 * t + a)
    (3 * t ^ 2 + 2 * a * t + b)
    (t ^ 3 + a * t ^ 2 + b * t + c)
  refine ⟨(k : ℤ) + t, ?_, ?_⟩
  · have ht : 0 < t := by
      dsimp [t]
      positivity
    exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg k) ht
  · intro hsqrt
    obtain ⟨m, hm⟩ := hsqrt
    apply hk
    refine ⟨m, ?_⟩
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have ha0 : 0 ≤ |a| := abs_nonneg a
    have hb0 : 0 ≤ |b| := abs_nonneg b
    have hc0 : 0 ≤ |c| := abs_nonneg c
    have ha : -|a| ≤ a := neg_abs_le a
    have hb : -|b| ≤ b := neg_abs_le b
    have hc : -|c| ≤ c := neg_abs_le c
    have hrad : (0 : ℤ) ≤ ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c := by
      dsimp [t]
      nlinarith [sq_nonneg ((k : ℤ) + (|a| + |b| + |c| + 1)),
        mul_nonneg (show (0 : ℤ) ≤ (k : ℤ) + (|a| + |b| + |c| + 1) by omega)
          (show (0 : ℤ) ≤ (k : ℤ) + |b| + |c| + 1 by omega)] -- non-rewrite step
    have hsquare_real :
        ((Real.sqrt ((((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 +
          b * ((k : ℤ) + t) + c : ℤ) : ℝ)) ^ 2) =
          ((((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 +
          b * ((k : ℤ) + t) + c : ℤ) : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast hrad)
    have hm' :
        Real.sqrt (((((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 +
          b * ((k : ℤ) + t) + c : ℤ) : ℝ)) = (m : ℝ) := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using hm
    rw [hm'] at hsquare_real
    have hsquare_int :
        m ^ 2 = ((k : ℤ) + t) ^ 3 + a * ((k : ℤ) + t) ^ 2 + b * ((k : ℤ) + t) + c := by
      exact_mod_cast hsquare_real
    rw [hsquare_int]
    ring -- non-rewrite step
