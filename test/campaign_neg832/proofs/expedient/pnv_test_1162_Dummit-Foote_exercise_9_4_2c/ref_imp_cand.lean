import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2c_assumed : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : Irreducible (Polynomial.C (1 : ℤ) + Polynomial.X + 6 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4) := by
  let q : Polynomial ℤ := X ^ 4 - 3 * X + 3
  have hq : Irreducible q := by
    have hmon : q.Monic := by
      dsimp [q]
      rw [show (X ^ 4 - 3 * X + 3 : Polynomial ℤ) = X ^ 4 - (3 * X - 3) by ring]
      apply (monic_X_pow 4).sub_of_left
      compute_degree <;> norm_num
    have hdeg : q.natDegree = 4 := by
      dsimp [q]
      compute_degree <;> norm_num
    have he : q.IsEisensteinAt (Ideal.span {3}) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hmon.leadingCoeff]
        norm_num [Ideal.mem_span_singleton]
      · intro n hn
        rw [hdeg] at hn
        interval_cases n <;> norm_num [q, Ideal.mem_span_singleton]
      · rw [Ideal.span_singleton_pow]
        norm_num [q, Ideal.mem_span_singleton]
    apply he.irreducible
    · exact (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
    · exact hmon.isPrimitive
    · omega
  have h := hq.map (Polynomial.taylorEquiv (1 : ℤ))
  change Irreducible (Polynomial.taylor 1 q) at h
  rw [Polynomial.taylor_apply] at h
  convert h using 1 <;> simp [q] <;> ring
