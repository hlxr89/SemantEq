import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : ℝ} (hα_irrat : Irrational α) : Dense (Set.range fun n : ℤ => α * ↑n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  have hd : Dense (Set.range fun n : ℤ => (Real.sqrt 2) * (n : ℝ)) :=
    dummy_assumed irrational_sqrt_two
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨x, ⟨n, rfl⟩, hx⟩ :=
    hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hsqrt_pos)
  rcases lt_or_ge n 1 with hn | hn
  · have hn0 : n ≤ 0 := by omega
    have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    have : Real.sqrt 2 * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hsqrt_pos) hn'
    exact (not_lt_of_ge this hx.1).elim
  · have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have : Real.sqrt 2 ≤ Real.sqrt 2 * (n : ℝ) := by
      nlinarith
    exact (not_lt_of_ge this hx.2).elim
