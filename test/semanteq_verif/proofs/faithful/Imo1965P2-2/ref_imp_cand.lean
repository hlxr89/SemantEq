import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1965_p2_assumed (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j)
    : ∀ i, x i = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
  (A 0 0 > 0) ∧ (A 1 1 > 0) ∧ (A 2 2 > 0) →
  (A 0 1 < 0) ∧ (A 0 2 < 0) ∧ (A 1 0 < 0) ∧ (A 1 2 < 0) ∧ (A 2 0 < 0) ∧ (A 2 1 < 0) →
  (A 0 0 + A 0 1 + A 0 2 > 0) ∧ (A 1 0 + A 1 1 + A 1 2 > 0) ∧ (A 2 0 + A 2 1 + A 2 2 > 0) →
  A.mulVec x = 0 →
  x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  rintro hdiag hoff hrows hmul
  have heqs : ∀ i, ∑ j : Fin 3, (A i j * x j) = 0 := by
    intro i
    exact congrFun hmul i
  have hab : ∀ i j, if i = j then 0 < A i j else A i j < 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  have hc : ∀ i, 0 < ∑ j : Fin 3, A i j := by
    intro i
    fin_cases i
    · simpa [Fin.sum_univ_succ, add_assoc] using hrows.1
    · simpa [Fin.sum_univ_succ, add_assoc] using hrows.2.1
    · simpa [Fin.sum_univ_succ, add_assoc] using hrows.2.2
  have h := imo1965_p2_assumed x A heqs hab hc
  exact ⟨h 0, h 1, h 2⟩
