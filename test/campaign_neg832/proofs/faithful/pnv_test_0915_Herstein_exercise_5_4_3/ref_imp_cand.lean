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
  obtain ⟨q, hq0, _, haq, hcoeff⟩ :=
    exercise_5_4_3_assumed (p := fun x : ℂ ↦
      x ^ 5 + √(2 : ℝ) * x ^ 3 + √(5 : ℝ) * x ^ 2 + √(7 : ℝ) * x + √(11 : ℝ)) rfl h
  have hcoeff' : ∀ n : ℕ, q.coeff n ∈ (algebraMap ℚ ℂ).range := by
    intro n
    by_cases hn : n ∈ q.support
    · obtain ⟨u, v, huv⟩ := hcoeff ⟨n, hn⟩
      refine ⟨(u : ℚ) / (v : ℚ), ?_⟩
      simpa using huv.symm
    · refine ⟨0, ?_⟩
      simpa using (Polynomial.notMem_support_iff.mp hn).symm
  obtain ⟨r, hr⟩ := (Polynomial.mem_map_range (algebraMap ℚ ℂ)).mpr hcoeff'
  refine ⟨r, ?_, ?_⟩
  · intro hr0
    apply hq0
    simpa [hr0] using hr.symm
  · have heval : q.eval a = 0 := (Polynomial.mem_roots hq0).mp haq
    rw [← hr] at heval
    simpa [Polynomial.aeval_def] using heval
