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
  let p : ℂ → ℂ := λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11
  obtain ⟨q, hq0, _hqdeg, hqa, hqcoeff⟩ := exercise_5_4_3_assumed (a := a) (p := p) rfl h
  have hc : ∀ n : ℕ, ∃ c : ℚ, q.coeff n = algebraMap ℚ ℂ c := by
    intro n
    by_cases hn : n ∈ q.support
    · obtain ⟨u, v, huv⟩ := hqcoeff ⟨n, hn⟩
      exact ⟨(u : ℚ) / (v : ℚ), by simpa only [map_div₀, map_intCast] using huv⟩
    · exact ⟨0, by simp only [mem_support_iff, ne_eq, not_not] at hn; simp only [hn, map_zero]⟩
  choose c hc using hc
  let r : Polynomial ℚ := q.support.sum fun n => Polynomial.monomial n (c n)
  have hrmap : r.map (algebraMap ℚ ℂ) = q := by
    dsimp only [r]
    rw [Polynomial.map_sum]
    simp_rw [Polynomial.map_monomial, ← hc]
    exact (as_sum_support q).symm
  refine ⟨r, ?_, ?_⟩
  · intro hr0
    apply hq0
    simpa only [hr0, Polynomial.map_zero] using hrmap.symm
  · rw [aeval_def, ← eval_map, hrmap]
    exact (mem_roots hq0).mp hqa
