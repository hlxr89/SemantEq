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
  obtain ⟨y, hy0, hy1, hy2, hyrec, n, hyn, hperiod⟩ :=
    (dummy_assumed (a := a))
  have heq : ∀ k : ℕ, x k = y k := by
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
      have hk3 : 3 ≤ k := by omega
      have hkpred : 2 ≤ k - 1 := by omega
      have hxrec := hxn (k - 1) hkpred
      have hyrec' := hyrec (k - 1) hkpred
      rw [show k - 1 + 1 = k by omega] at hxrec hyrec'
      rw [ih (k - 1) (by omega), ih (k - 1 - 1) (by omega),
        ih (k - 1 - 2) (by omega)] at hxrec
      exact hxrec.trans hyrec'.symm
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    linarith [hy0, hyn]
  refine ⟨n, hn, ?_⟩
  intro m
  rw [Nat.add_comm, heq (n + m), heq m]
  exact hperiod m
