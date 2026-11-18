import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
  (A 0 0 > 0) ∧ (A 1 1 > 0) ∧ (A 2 2 > 0) →
  (A 0 1 < 0) ∧ (A 0 2 < 0) ∧ (A 1 0 < 0) ∧ (A 1 2 < 0) ∧ (A 2 0 < 0) ∧ (A 2 1 < 0) →
  (A 0 0 + A 0 1 + A 0 2 > 0) ∧ (A 1 0 + A 1 1 + A 1 2 > 0) ∧ (A 2 0 + A 2 1 + A 2 2 > 0) →
  A.mulVec x = 0 →
  x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1965_p2 (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j)
    : ∀ i, x i = 0 := by
  have hdiag : (a 0 0 > 0) ∧ (a 1 1 > 0) ∧ (a 2 2 > 0) := by
    simpa using ⟨hab 0 0, hab 1 1, hab 2 2⟩
  have hoff : (a 0 1 < 0) ∧ (a 0 2 < 0) ∧ (a 1 0 < 0) ∧ (a 1 2 < 0) ∧ (a 2 0 < 0) ∧ (a 2 1 < 0) := by
    simpa using ⟨hab 0 1, hab 0 2, hab 1 0, hab 1 2, hab 2 0, hab 2 1⟩
  have hrows : (a 0 0 + a 0 1 + a 0 2 > 0) ∧ (a 1 0 + a 1 1 + a 1 2 > 0) ∧ (a 2 0 + a 2 1 + a 2 2 > 0) := by
    constructor
    · simpa [Fin.sum_univ_succ, add_assoc] using hc 0
    constructor
    · simpa [Fin.sum_univ_succ, add_assoc] using hc 1
    · simpa [Fin.sum_univ_succ, add_assoc] using hc 2
  have hmul : Matrix.mulVec a x = 0 := by
    funext i
    exact heqs i
  have h := problem_statement_assumed a x hdiag hoff hrows hmul
  intro i
  fin_cases i <;> simp_all
