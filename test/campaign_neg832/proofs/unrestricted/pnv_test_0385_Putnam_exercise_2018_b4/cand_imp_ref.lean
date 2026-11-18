import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} (seq : ℕ → ℝ) (hseq : seq 0 = 0) : ∃ N, ∀ n ≥ N, seq (n + 2) = seq n ∧ seq (n + 1) = seq (n + 1) ∧ seq n = seq (n - 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  obtain ⟨N, hN⟩ := dummy_assumed (a := (0 : ℝ)) (fun n : ℕ => (n : ℝ)) (by norm_num)
  have hbad := (hN N (by omega)).1
  norm_num at hbad
