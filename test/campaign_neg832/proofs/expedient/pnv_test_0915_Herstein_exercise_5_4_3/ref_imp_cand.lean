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
  obtain ⟨q, hq, _, ha, hc⟩ := exercise_5_4_3_assumed
    (p := λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11) rfl h
  classical
  have hcoeff : ∀ n : ℕ, ∃ c : ℚ, (c : ℂ) = q.coeff n := by
    intro n
    by_cases hn : n ∈ q.support
    · obtain ⟨z, w, hzw⟩ := hc ⟨n, hn⟩
      refine ⟨z / w, ?_⟩
      push_cast
      exact hzw.symm
    · refine ⟨0, ?_⟩
      rw [mem_support_iff] at hn
      norm_num
      exact (not_ne_iff.mp hn).symm
  choose c hc using hcoeff
  let r : Polynomial ℚ := ∑ n ∈ q.support, monomial n (c n)
  have hrmap : r.map (algebraMap ℚ ℂ) = q := by
    ext n
    by_cases hn : n ∈ q.support
    · simp [r, coeff_monomial, hn, hc]
    · rw [mem_support_iff] at hn
      simp [r, coeff_monomial, not_ne_iff.mp hn]
  refine ⟨r, ?_, ?_⟩
  · intro hr
    apply hq
    rw [← hrmap, hr]
    simp
  · rw [aeval_def, ← Polynomial.eval_map, hrmap]
    exact (Polynomial.mem_roots hq).mp ha
