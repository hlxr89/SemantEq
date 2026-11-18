import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} : ∃ (x : ℕ → ℝ), x 0 = 1 ∧ x 1 = a ∧ x 2 = a ∧ (∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) ∧ (∃ n : ℕ, x n = 0 ∧ ∀ m : ℕ, x (n + m) = x m) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  obtain ⟨y, hy0, hy1, hy2, hyn, n, hn0, hnper⟩ := dummy_assumed (a := a)
  have hxy : ∀ k : ℕ, x k = y k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hk0 : k = 0
        · subst k
          exact hx0.trans hy0.symm
        by_cases hk1 : k = 1
        · subst k
          exact hx1.trans hy1.symm
        by_cases hk2 : k = 2
        · subst k
          exact hx2.trans hy2.symm
        · calc
            x k = x ((k - 1) + 1) := by congr 1 <;> omega
            _ = 2 * x (k - 1) * x ((k - 1) - 1) - x ((k - 1) - 2) :=
              hxn (k - 1) (by omega)
            _ = 2 * y (k - 1) * y ((k - 1) - 1) - y ((k - 1) - 2) := by
              rw [ih (k - 1) (by omega), ih ((k - 1) - 1) (by omega),
                ih ((k - 1) - 2) (by omega)]
            _ = y ((k - 1) + 1) := (hyn (k - 1) (by omega)).symm
            _ = y k := by congr 1 <;> omega
  refine ⟨n, ?_, ?_⟩
  · intro hn
    subst n
    have : y 0 = 0 := hn0
    linarith [hy0]
  · intro m
    rw [hxy (m + n), hxy m]
    simpa [Nat.add_comm] using hnper m
