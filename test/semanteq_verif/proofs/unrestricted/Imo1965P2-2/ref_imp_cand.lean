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
  rintro ⟨h00, h11, h22⟩
    ⟨h01, h02, h10, h12, h20, h21⟩
    ⟨hr0, hr1, hr2⟩ hmul
  have hz := imo1965_p2_assumed x A (by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hmul i) (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]) (by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_three, hr0, hr1, hr2])
  exact ⟨hz 0, hz 1, hz 2⟩
