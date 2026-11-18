import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_4_3_assumed {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a : ℂ) (h : a ^ 5 + √(2 : ℝ) * a ^ 3 + √(5 : ℝ) * a ^ 2 + √(7 : ℝ) * a + √(11 : ℝ) = 0) : IsAlgebraic ℚ a := by
  obtain ⟨q, hq, _hdegree, ha, hcoeff⟩ := exercise_5_4_3_assumed
    (a := a)
    (p := fun x : ℂ => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
    rfl (by simpa using h)
  have hc : ∀ n : ℕ, ∃ r : ℚ, (r : ℂ) = q.coeff n := by
    intro n
    by_cases hn : n ∈ q.support
    · obtain ⟨z, w, hzw⟩ := hcoeff ⟨n, hn⟩
      refine ⟨(z : ℚ) / (w : ℚ), ?_⟩
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
      exact hzw.symm
    · refine ⟨0, ?_⟩
      have hz : q.coeff n = 0 := by
        simpa [Polynomial.mem_support_iff] using hn
      simpa only [Rat.cast_zero] using hz.symm
  choose c hc using hc
  let r : Polynomial ℚ := q.sum fun n _ => monomial n (c n)
  have hrmap : r.map (algebraMap ℚ ℂ) = q := by
    change (Polynomial.map (algebraMap ℚ ℂ)
      (∑ n ∈ q.support, monomial n (c n))) = q
    rw [Polynomial.map_sum]
    calc
      ∑ n ∈ q.support, Polynomial.map (algebraMap ℚ ℂ) (monomial n (c n)) =
          ∑ n ∈ q.support, monomial n (q.coeff n) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [map_monomial]
            exact congrArg (monomial n) (hc n)
      _ = q := q.sum_monomial_eq
  refine ⟨r, ?_, ?_⟩
  · intro hr
    apply hq
    simpa [hr] using hrmap.symm
  · rw [aeval_def, ← eval_map, hrmap]
    exact (mem_roots'.mp ha).2
